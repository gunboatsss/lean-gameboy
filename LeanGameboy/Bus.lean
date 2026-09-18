/-
  LeanGameboy.Bus — system interconnect: full memory map, CPU executor,
  interrupt dispatch, APU/PPU/Timer register handling, OAM DMA.

  Everything is pure: `GBState` in, `GBState` out. The `IO` frontend
  (SDL / headless) lives in `Emu` + `Main`.
-/
import LeanGameboy.Basic
import LeanGameboy.Cpu.Regs
import LeanGameboy.Cpu.Decode
import LeanGameboy.Cartridge.Header
import LeanGameboy.Cartridge.Mbc
import LeanGameboy.Cgb
import LeanGameboy.Timer
import LeanGameboy.Interrupts
import LeanGameboy.Joypad
import LeanGameboy.Serial
import LeanGameboy.Ppu
import LeanGameboy.Framebuffer
import LeanGameboy.Apu

namespace GB

/-- Complete DMG+CGB system state. -/
structure GBState where
  regs : Regs := {}
  rom : ByteArray := ByteArray.empty
  mbc : MbcState := {}
  ram : ExtRam := {}
  -- CGB-sized memories (uniform for both modes: 8×4 KiB WRAM banks,
  -- 2×8 KiB VRAM banks; DMG games simply never select past bank 1/0)
  wram : ByteArray := ByteArray.empty
  vram : ByteArray := ByteArray.empty
  oam : ByteArray := ByteArray.empty
  hram : ByteArray := ByteArray.empty
  ie : UInt8 := 0
  if_ : UInt8 := 0xE0
  timer : TimerState := {}
  ppu : PpuState := {}
  apu : ApuState := {}
  joy : JoypadState := {}
  serial : SerialState := {}
  fb : Array UInt32 := fbBlank
  cycles : Nat := 0
  haltBug : Bool := false
  -- CGB extensions
  cgb : Bool := false          -- true when running a CGB cartridge
  doubleSpeed : Bool := false  -- KEY1 double-speed active
  speedPrep : Bool := false    -- KEY1 speed-switch armed
  vbk : UInt8 := 0             -- VRAM bank select (bit 0)
  svbk : UInt8 := 0            -- WRAM bank select (low 3 bits, 0 → 1)
  bgpi : UInt8 := 0            -- BG palette index (bit 7 = auto-inc)
  obpi : UInt8 := 0            -- OBJ palette index (bit 7 = auto-inc)
  bgPal : Array UInt16 := palFresh
  obPal : Array UInt16 := palFresh
  hdma : HdmaState := {}

/-- Fresh state for a ROM image (boot ROM skipped, DMG/CGB defaults
    selected from the cartridge CGB flag). -/
def GBState.fresh (rom : ByteArray) : GBState :=
  let h := parseHeader rom
  let cgb := match h.cgb with | .Dmg => false | _ => true
  let base : GBState := {}
  { base with
    cgb := cgb
    regs := if cgb then Regs.bootDefaultsCgb else Regs.bootDefaults
    rom := rom
    mbc := MbcState.ofHeader h
    ram := ExtRam.fresh h.ramBanks
    wram := ByteArray.mk (Array.mk (List.replicate wramCgbSize 0))
    vram := ByteArray.mk (Array.mk (List.replicate vramCgbSize 0))
    oam := ByteArray.mk (Array.mk (List.replicate 0xA0 0))
    hram := ByteArray.mk (Array.mk (List.replicate 0x7F 0))
    bgPal := palFresh
    obPal := palFresh
    fb := fbBlank }

/-! ## APU register access -/

/-- Reconstruct readable APU registers from channel state (write-only
    bits read back as 1, per hardware). -/
def apuRead (s : GBState) (addr : Nat) : UInt8 :=
  let a := s.apu
  match addr with
  | 0xFF10 => w8 (a.ch1.sweepPeriod * 16 + (if a.ch1.sweepDir then 8 else 0) + a.ch1.sweepShift) ||| 0x80
  | 0xFF11 => w8 (a.ch2.duty * 64) ||| 0x3F
  | 0xFF12 => w8 (a.ch2.initVol * 16 + (if a.ch2.envDir then 8 else 0) + a.ch2.envPeriod)
  | 0xFF13 => 0xFF
  | 0xFF14 => w8 ((a.ch1.freq / 256)) ||| 0xBF
  | 0xFF16 => w8 (a.ch2.duty * 64) ||| 0x3F
  | 0xFF17 => w8 (a.ch2.initVol * 16 + (if a.ch2.envDir then 8 else 0) + a.ch2.envPeriod)
  | 0xFF18 => 0xFF
  | 0xFF19 => 0xBF
  | 0xFF1A => (if a.ch3.dac then 0x80 else 0) ||| 0x7F
  | 0xFF1B => 0xFF
  | 0xFF1C => w8 (a.ch3.volCode * 32) ||| 0x9F
  | 0xFF1D => 0xFF
  | 0xFF1E => 0xBF
  | 0xFF20 => 0xFF
  | 0xFF21 => w8 (a.ch4.initVol * 16 + (if a.ch4.envDir then 8 else 0) + a.ch4.envPeriod)
  | 0xFF22 => w8 (a.ch4.shift * 16 + (if a.ch4.width then 8 else 0) + a.ch4.divisor)
  | 0xFF23 => 0xBF
  | 0xFF24 => a.nr50
  | 0xFF25 => a.nr51
  | 0xFF26 => (if a.powered then 0x80 else 0) ||| 0x70 |||
      (if a.ch4.enable then 8 else 0) ||| (if a.ch3.enable then 4 else 0) |||
      (if a.ch2.enable then 2 else 0) ||| (if a.ch1.enable then 1 else 0)
  | n =>
    if 0xFF30 <= n && n < 0xFF40 then
      if (n - 0xFF30) < a.ch3.wave.size then a.ch3.wave[n - 0xFF30]! else 0xFF
    else 0xFF

/-- Trigger a pulse channel (CH1/CH2 shared logic). -/
def pulseTrigger (c : PulseCh) (isCh1 : Bool) : PulseCh :=
  let c1 := { c with enable := c.dac }
  let c2 := if c1.len == 0 then { c1 with len := 64 } else c1
  let c3 := { c2 with vol := c2.initVol, envTimer := c2.envPeriod }
  if isCh1 then
    let c4 := { c3 with
      shadow := c3.freq
      sweepTimer := if c3.sweepPeriod == 0 then 8 else c3.sweepPeriod
      sweepEnable := c3.sweepPeriod != 0 || c3.sweepShift != 0 }
    c4
  else c3

/-- Handle a write to an APU register. -/
def apuWrite (s : GBState) (addr : Nat) (v : UInt8) : GBState :=
  -- flush pending channel-phase time first: period/frequency writes
  -- and triggers observe phase timing, so lazily-deferred phases
  -- must be applied before the write takes effect
  let a := s.apu.flush
  let n := v.toNat
  -- writes are ignored while powered off (except NR52 + wave RAM)
  if !a.powered && addr != 0xFF26 && !(0xFF30 <= addr && addr < 0xFF40) then s
  else
    let a' : ApuState :=
      match addr with
      | 0xFF10 => { a with ch1 := { a.ch1 with
          sweepPeriod := (n / 16) % 8
          sweepDir := (n / 8) % 2 == 1
          sweepShift := n % 8 } }
      | 0xFF11 => { a with ch1 := { a.ch1 with duty := (n / 64) % 4, len := 64 - n % 64 } }
      | 0xFF12 => { a with ch1 := { a.ch1 with
          initVol := (n / 16) % 16
          envDir := (n / 8) % 2 == 1
          envPeriod := n % 8
          dac := (n &&& 0xF8) != 0 } }
      | 0xFF13 => { a with ch1 := { a.ch1 with freq := (a.ch1.freq / 256) * 256 + n } }
      | 0xFF14 => { a with ch1 :=
          let c := { a.ch1 with
            freq := (n % 8) * 256 + a.ch1.freq % 256
            lenEnable := n / 64 % 2 == 1 }
          if n / 128 % 2 == 1 then pulseTrigger c true else c }
      | 0xFF16 => { a with ch2 := { a.ch2 with duty := (n / 64) % 4, len := 64 - n % 64 } }
      | 0xFF17 => { a with ch2 := { a.ch2 with
          initVol := (n / 16) % 16
          envDir := (n / 8) % 2 == 1
          envPeriod := n % 8
          dac := (n &&& 0xF8) != 0 } }
      | 0xFF18 => { a with ch2 := { a.ch2 with freq := (a.ch2.freq / 256) * 256 + n } }
      | 0xFF19 => { a with ch2 :=
          let c := { a.ch2 with
            freq := (n % 8) * 256 + a.ch2.freq % 256
            lenEnable := n / 64 % 2 == 1 }
          if n / 128 % 2 == 1 then pulseTrigger c false else c }
      | 0xFF1A => { a with ch3 := { a.ch3 with dac := n / 128 == 1 } }
      | 0xFF1B => { a with ch3 := { a.ch3 with len := 256 - n } }
      | 0xFF1C => { a with ch3 := { a.ch3 with volCode := (n / 32) % 4 } }
      | 0xFF1D => { a with ch3 := { a.ch3 with freq := (a.ch3.freq / 256) * 256 + n } }
      | 0xFF1E => { a with ch3 :=
          let c := { a.ch3 with
            freq := (n % 8) * 256 + a.ch3.freq % 256
            lenEnable := n / 64 % 2 == 1 }
          if n / 128 % 2 == 1 then
            let c2 := { c with enable := c.dac, pos := 0 }
            if c2.len == 0 then { c2 with len := 256 } else c2
          else c }
      | 0xFF20 => { a with ch4 := { a.ch4 with len := 64 - n % 64 } }
      | 0xFF21 => { a with ch4 := { a.ch4 with
          initVol := (n / 16) % 16
          envDir := (n / 8) % 2 == 1
          envPeriod := n % 8
          dac := (n &&& 0xF8) != 0 } }
      | 0xFF22 => { a with ch4 := { a.ch4 with
          shift := (n / 16) % 16
          width := (n / 8) % 2 == 1
          divisor := n % 8 } }
      | 0xFF23 => { a with ch4 :=
          let c := { a.ch4 with lenEnable := n / 64 % 2 == 1 }
          if n / 128 % 2 == 1 then
            let c2 := { c with
              enable := c.dac
              lfsr := 0x7FFF
              vol := c.initVol
              envTimer := c.envPeriod }
            if c2.len == 0 then { c2 with len := 64 } else c2
          else c }
      | 0xFF24 => { a with nr50 := v }
      | 0xFF25 => { a with nr51 := v }
      | 0xFF26 =>
        if n / 128 == 1 then
          if a.powered then a
          else { a with powered := true, seqStep := 0 }
        else
          { ({} : ApuState) with nr52 := 0 }  -- power off: clear everything
      | _ => a
    -- wave RAM
    let a'' : ApuState :=
      if 0xFF30 <= addr && addr < 0xFF40 then
        let i := addr - 0xFF30
        { a' with ch3 := { a'.ch3 with wave := a'.ch3.wave.set! i v } }
      else a'
    { s with apu := a'' }

/-! ## Memory map -/

/-- Read a byte from the bus. -/
def busRead (s : GBState) (addr16 : UInt16) : UInt8 :=
  let addr := addr16.toNat
  if addr < 0x8000 then cartRead s.rom s.mbc addr
  else if addr < 0xA000 then
    if s.ppu.mode == 3 then 0xFF else vramRead s.vram s.vbk addr
  else if addr < 0xC000 then extRamRead s.ram s.mbc addr
  else if addr < 0xE000 then wramRead s.wram s.svbk addr
  else if addr < 0xFE00 then wramRead s.wram s.svbk (addr - 0x2000)
  else if addr < 0xFEA0 then
    if s.ppu.mode >= 2 then 0xFF else bget s.oam (addr - 0xFE00)
  else if addr < 0xFF00 then 0xFF
  else if addr < 0xFF80 then
    match addr with
    | 0xFF00 => s.joy.read
    | 0xFF01 => s.serial.sb
    | 0xFF02 => s.serial.sc ||| 0x7C
    | 0xFF04 => s.timer.div
    | 0xFF05 => s.timer.tima
    | 0xFF06 => s.timer.tma
    | 0xFF07 => s.timer.tac ||| 0xF8
    | 0xFF0F => s.if_
    | 0xFF40 => s.ppu.lcdc
    | 0xFF41 => s.ppu.stat ||| 0x80
    | 0xFF42 => s.ppu.scy
    | 0xFF43 => s.ppu.scx
    | 0xFF44 => s.ppu.ly
    | 0xFF45 => s.ppu.lyc
    | 0xFF46 => 0xFF -- DMA write-only
    | 0xFF47 => s.ppu.bgp
    | 0xFF48 => s.ppu.obp0
    | 0xFF49 => s.ppu.obp1
    | 0xFF4A => s.ppu.wy
    | 0xFF4B => s.ppu.wx
    | 0xFF4D => -- KEY1: bit 7 = speed, bits 6-1 read as 1, bit 0 = armed
      (if s.doubleSpeed then 0x80 else 0) ||| 0x7E |||
        (if s.speedPrep then 0x01 else 0x00)
    | 0xFF4F => s.vbk ||| 0xFE
    | 0xFF51 => 0xFF -- HDMA1..4 write-only
    | 0xFF52 => 0xFF
    | 0xFF53 => 0xFF
    | 0xFF54 => 0xFF
    | 0xFF55 => s.hdma.statusReg
    | 0xFF68 => s.bgpi
    | 0xFF69 => palReadByte s.bgPal (s.bgpi.toNat % 64)
    | 0xFF6A => s.obpi
    | 0xFF6B => palReadByte s.obPal (s.obpi.toNat % 64)
    | 0xFF70 => s.svbk ||| 0xF8
    | n =>
      if 0xFF10 <= n && n <= 0xFF3F then apuRead s n
      else 0xFF
  else if addr < 0xFFFF then bget s.hram (addr - 0xFF80)
  else s.ie

/-- OAM DMA: copy 160 bytes from `src` into OAM. -/
def oamDma (s : GBState) (src : Nat) : GBState :=
  let bytes := List.range 160 |>.map fun i =>
    busRead s (w16 (src + i))
  let oam := (List.range 160).foldl
    (fun (o : ByteArray) i => bset o i bytes[i]!) s.oam
  { s with oam := oam }

/-- One HDMA byte copy (fold step): VRAM `dst+i` ← bus `src+i`.
    Source reads go through the full bus (bank-aware); the
    destination low nibble is forced to 0. -/
def hdmaCopyStep (src dst : Nat) (st : GBState) (i : Nat) : GBState :=
  let b := busRead st (w16 (src + i))
  { st with vram := vramWrite st.vram st.vbk (0x8000 + ((dst + i) % 0x2000)) b }

/-- Copy one 16-byte HDMA block. -/
def hdmaBlock (s : GBState) (src dst : Nat) : GBState :=
  (List.range 16).foldl (hdmaCopyStep src dst) s

/-- Advance an HBlank HDMA by one block (called per completed visible
    scanline while active). -/
def hdmaHblank (s : GBState) : GBState :=
  let h := s.hdma
  if !h.active then s
  else
    let s1 := hdmaBlock s h.src h.dst
    let left := if h.remaining <= 16 then 0 else h.remaining - 16
    { s1 with hdma := { h with
      src := (h.src + 16) % 65536
      dst := (h.dst + 16) % 0x2000
      remaining := left
      active := left != 0 } }

/-- Run a GDMA (general-purpose DMA) of `len` bytes immediately.
    Returns updated state + stall cost in CPU M-cycles
    (2 T-cycles/byte at wall clock: len/2 normal, len double). -/
def hdmaGdma (s : GBState) (len : Nat) : GBState × Nat :=
  let blocks := len / 16
  let rec loop : Nat → GBState → GBState
    | 0, st => st
    | k + 1, st =>
      let st1 := hdmaBlock st st.hdma.src st.hdma.dst
      loop k { st1 with hdma := { st1.hdma with
        src := (st1.hdma.src + 16) % 65536
        dst := (st1.hdma.dst + 16) % 0x2000
        remaining := if st1.hdma.remaining <= 16 then 0
                     else st1.hdma.remaining - 16 } }
  let s1 := loop blocks s
  let s2 := { s1 with hdma := { s1.hdma with remaining := 0, active := false } }
  (s2, if s.doubleSpeed then blocks * 16 else blocks * 8)

/-- Write a byte to the bus. Returns updated state + extra M-cycles
    (OAM DMA costs 160). -/
def busWrite (s : GBState) (addr16 : UInt16) (v : UInt8) : GBState × Nat :=
  let addr := addr16.toNat
  if addr < 0x8000 then ({ s with mbc := cartWrite s.mbc addr v }, 0)
  else if addr < 0xA000 then
    if s.ppu.mode == 3 then (s, 0)
    else ({ s with vram := vramWrite s.vram s.vbk addr v }, 0)
  else if addr < 0xC000 then ({ s with ram := extRamWrite s.ram s.mbc addr v }, 0)
  else if addr < 0xE000 then ({ s with wram := wramWrite s.wram s.svbk addr v }, 0)
  else if addr < 0xFE00 then
    ({ s with wram := wramWrite s.wram s.svbk (addr - 0x2000) v }, 0)
  else if addr < 0xFEA0 then
    if s.ppu.mode >= 2 then (s, 0)
    else ({ s with oam := bset s.oam (addr - 0xFE00) v }, 0)
  else if addr < 0xFF00 then (s, 0)
  else if addr < 0xFF80 then
    match addr with
    | 0xFF00 => ({ s with joy := s.joy.write v }, 0)
    | 0xFF01 => ({ s with serial := { s.serial with sb := v } }, 0)
    | 0xFF02 => ({ s with serial := ({ s.serial with sc := v }.maybeStart) }, 0)
    | 0xFF04 => ({ s with timer := s.timer.writeDiv }, 0)
    | 0xFF05 => ({ s with timer := { s.timer with tima := v } }, 0)
    | 0xFF06 => ({ s with timer := { s.timer with tma := v } }, 0)
    | 0xFF07 =>
      let tac := v &&& 0x07
      let lvl := TimerState.andLevel s.timer.divInternal tac
      let t := s.timer
      let (tima', irq') :=
        if t.prevAnd && !lvl then
          if t.tima == 0xFF then (t.tma, true) else (t.tima + 1, t.irq)
        else (t.tima, t.irq)
      ({ s with timer := { t with tac := tac, tima := tima', prevAnd := lvl, irq := irq' } }, 0)
    | 0xFF0F => ({ s with if_ := v ||| 0xE0 }, 0)
    | 0xFF40 =>
      let p := s.ppu
      let p' := if bitGet p.lcdc 7 && !bitGet v 7 then
        { p with
          lcdc := v
          ly := 0
          dots := 0
          mode := 0
          stat := p.stat &&& 0xF8
          statLine := false }
        else { p with lcdc := v }
      ({ s with ppu := p' }, 0)
    | 0xFF41 => ({ s with ppu := { s.ppu with
        stat := (v &&& 0x78) ||| (s.ppu.stat &&& 0x87) } }, 0)
    | 0xFF42 => ({ s with ppu := { s.ppu with scy := v } }, 0)
    | 0xFF43 => ({ s with ppu := { s.ppu with scx := v } }, 0)
    | 0xFF44 => (s, 0) -- LY read-only
    | 0xFF45 =>
      let p := { s.ppu with lyc := v }
      let stat := (p.stat &&& 0xFB) ||| (if p.ly == p.lyc then (0x04 : UInt8) else 0x00)
      ({ s with ppu := { p with stat := stat } }, 0)
    | 0xFF46 => (oamDma s (v.toNat * 0x100), 160)
    | 0xFF47 => ({ s with ppu := { s.ppu with bgp := v } }, 0)
    | 0xFF48 => ({ s with ppu := { s.ppu with obp0 := v } }, 0)
    | 0xFF49 => ({ s with ppu := { s.ppu with obp1 := v } }, 0)
    | 0xFF4A => ({ s with ppu := { s.ppu with wy := v } }, 0)
    | 0xFF4B => ({ s with ppu := { s.ppu with wx := v } }, 0)
    | 0xFF4D => ({ s with speedPrep := v.toNat % 2 == 1 }, 0) -- KEY1: bit 0 arms
    | 0xFF4F => ({ s with vbk := v &&& 0x01 }, 0)
    | 0xFF51 => ({ s with hdma := { s.hdma with
        src := ((v.toNat * 256) + s.hdma.src % 256) % 65536 } }, 0)
    | 0xFF52 => ({ s with hdma := { s.hdma with
        src := (s.hdma.src / 256) * 256 + (v.toNat / 16) * 16 } }, 0)
    | 0xFF53 => ({ s with hdma := { s.hdma with
        dst := ((v.toNat % 32) * 256 + s.hdma.dst % 256) % 0x2000 } }, 0)
    | 0xFF54 => ({ s with hdma := { s.hdma with
        dst := ((s.hdma.dst / 256) * 256 + (v.toNat / 16) * 16) % 0x2000 } }, 0)
    | 0xFF55 =>
      if bitGet v 7 then
        if s.hdma.active then
          -- HBlank DMA in progress: write with bit 7 cancels it
          ({ s with hdma := { s.hdma with active := false } }, 0)
        else
          -- start HBlank DMA (first block transfers at next HBlank)
          ({ s with hdma := { s.hdma with
            remaining := HdmaState.totalLen v, active := true } }, 0)
      else
        if s.hdma.active then
          -- GDMA write with bit 7 clear cancels an active HBlank DMA
          ({ s with hdma := { s.hdma with active := false } }, 0)
        else
          let (s1, cost) := hdmaGdma
            { s with hdma := { s.hdma with
              remaining := HdmaState.totalLen v } }
            (HdmaState.totalLen v)
          (s1, cost)
    | 0xFF68 => ({ s with bgpi := v }, 0)
    | 0xFF69 =>
      let idx := s.bgpi.toNat % 64
      ({ s with
        bgPal := palWriteByte s.bgPal idx v
        bgpi := palAutoInc s.bgpi }, 0)
    | 0xFF6A => ({ s with obpi := v }, 0)
    | 0xFF6B =>
      let idx := s.obpi.toNat % 64
      ({ s with
        obPal := palWriteByte s.obPal idx v
        obpi := palAutoInc s.obpi }, 0)
    | 0xFF70 => ({ s with svbk := v &&& 0x07 }, 0)
    | n =>
      if 0xFF10 <= n && n <= 0xFF3F then (apuWrite s n v, 0)
      else (s, 0)
  else if addr < 0xFFFF then
    ({ s with hram := bset s.hram (addr - 0xFF80) v }, 0)
  else ({ s with ie := v }, 0)

/-! ## CPU helpers -/

def read16 (s : GBState) (addr : UInt16) : UInt16 :=
  join16 (busRead s (addr + 1)) (busRead s addr)

def write16 (s : GBState) (addr : UInt16) (v : UInt16) : GBState × Nat :=
  let (s1, c1) := busWrite s addr (loByte v)
  let (s2, c2) := busWrite s1 (addr + 1) (hiByte v)
  (s2, c1 + c2)

def push (s : GBState) (v : UInt16) : GBState × Nat :=
  let sp := s.regs.sp - 2
  let s1 := { s with regs := { s.regs with sp := sp } }
  let (s2, c) := write16 s1 sp v
  (s2, c)

def pop (s : GBState) : GBState × UInt16 :=
  let v := read16 s s.regs.sp
  ({ s with regs := { s.regs with sp := s.regs.sp + 2 } }, v)

def getR8 (s : GBState) : R8 → UInt8
  | .B => s.regs.b | .C => s.regs.c | .D => s.regs.d | .E => s.regs.e
  | .H => s.regs.h | .L => s.regs.l | .HLM => busRead s s.regs.hl
  | .A => s.regs.a

def setR8 (s : GBState) : R8 → UInt8 → GBState × Nat
  | .B, v => ({ s with regs := { s.regs with b := v } }, 0)
  | .C, v => ({ s with regs := { s.regs with c := v } }, 0)
  | .D, v => ({ s with regs := { s.regs with d := v } }, 0)
  | .E, v => ({ s with regs := { s.regs with e := v } }, 0)
  | .H, v => ({ s with regs := { s.regs with h := v } }, 0)
  | .L, v => ({ s with regs := { s.regs with l := v } }, 0)
  | .HLM, v => busWrite s s.regs.hl v
  | .A, v => ({ s with regs := { s.regs with a := v } }, 0)

def getR16 (s : GBState) : R16 → UInt16
  | .BC => s.regs.bc | .DE => s.regs.de | .HL => s.regs.hl | .SP => s.regs.sp

def setR16 (s : GBState) : R16 → UInt16 → GBState
  | .BC, v => { s with regs := s.regs.setBC v }
  | .DE, v => { s with regs := s.regs.setDE v }
  | .HL, v => { s with regs := s.regs.setHL v }
  | .SP, v => { s with regs := { s.regs with sp := v } }

def getRP (s : GBState) : RP → UInt16
  | .BC => s.regs.bc | .DE => s.regs.de | .HL => s.regs.hl | .AF => s.regs.af

def setRP (s : GBState) : RP → UInt16 → GBState
  | .BC, v => { s with regs := s.regs.setBC v }
  | .DE, v => { s with regs := s.regs.setDE v }
  | .HL, v => { s with regs := s.regs.setHL v }
  | .AF, v => { s with regs := s.regs.setAF v }

def condTrue (s : GBState) : Cond → Bool
  | .NZ => !s.regs.z | .Z => s.regs.z | .NC => !s.regs.cf | .C => s.regs.cf

/-- Apply an ALU op to A with operand `v`. -/
def alu (s : GBState) (op : AluOp) (v : UInt8) : GBState :=
  let r := s.regs
  let set (a : UInt8) (z n h c : Bool) : GBState :=
    { s with regs := { r with a := a, z := z, n := n, hf := h, cf := c } }
  match op with
  | .Add =>
    let res := add8 r.a v
    set res.val (res.val == 0) false res.halfCarry res.carry
  | .Adc =>
    let res := add8 r.a v r.cf
    set res.val (res.val == 0) false res.halfCarry res.carry
  | .Sub =>
    let res := sub8 r.a v
    set res.val (res.val == 0) true res.halfCarry res.carry
  | .Sbc =>
    let res := sub8 r.a v r.cf
    set res.val (res.val == 0) true res.halfCarry res.carry
  | .And => set (r.a &&& v) ((r.a &&& v) == 0) false true false
  | .Xor => set (r.a ^^^ v) ((r.a ^^^ v) == 0) false false false
  | .Or => set (r.a ||| v) ((r.a ||| v) == 0) false false false
  | .Cp =>
    let res := sub8 r.a v
    set r.a (res.val == 0) true res.halfCarry res.carry

/-- Decimal adjust A (the famously tricky one). -/
def daa (s : GBState) : GBState :=
  let r := s.regs
  let (a1, c1) :=
    if !r.n then
      let (x, c) := if r.cf || r.a.toNat > 0x99 then (r.a + 0x60, true) else (r.a, r.cf)
      let (y, _) := if r.hf || (x.toNat % 16) > 9 then (x + 0x06, true) else (x, false)
      (y, c)
    else
      let x := if r.cf then r.a - 0x60 else r.a
      let y := if r.hf then x - 0x06 else x
      (y, r.cf)
  { s with regs := { r with a := a1, z := a1 == 0, hf := false, cf := c1 } }

/-- Execute one CB-prefixed op. Returns extra M-cycles (0; base in table). -/
def execCB (s : GBState) (op : RotOp) (r : R8) : GBState × Nat :=
  let x := getR8 s r
  let regs := s.regs
  let done (v : UInt8) (c : Bool) : GBState × Nat :=
    let (s1, cx) := setR8 s r v
    let st := { s1 with regs := { s1.regs with
      z := v == 0
      n := false
      hf := false
      cf := c } }
    (st, cx)
  match op with
  | .Rlc =>
    let c := bitGet x 7
    let v := (x <<< 1) ||| (if c then 1 else 0)
    done v c
  | .Rrc =>
    let c := bitGet x 0
    let v := (x >>> 1) ||| (if c then 0x80 else 0)
    done v c
  | .Rl =>
    let c := bitGet x 7
    let v := (x <<< 1) ||| (if regs.cf then 1 else 0)
    done v c
  | .Rr =>
    let c := bitGet x 0
    let v := (x >>> 1) ||| (if regs.cf then 0x80 else 0)
    done v c
  | .Sla =>
    let c := bitGet x 7
    done (x <<< 1) c
  | .Sra =>
    let c := bitGet x 0
    done ((x >>> 1) ||| (x &&& 0x80)) c
  | .Swap =>
    done ((x <<< 4) ||| (x >>> 4)) false
  | .Srl =>
    let c := bitGet x 0
    done (x >>> 1) c

/-! ## Instruction execution -/

/-- Signed 8-bit offset → signed Int. -/
def off8 (v : UInt8) : Int := v.toNat - (if v.toNat >= 128 then 256 else 0)

/-- Add a signed offset to a PC value. -/
def pcRel (pc : UInt16) (e : UInt8) : UInt16 :=
  w16 ((((pc.toNat : Int) + off8 e + 65536) % 65536).toNat)

/-- Signed offset added to SP, with half-carry/carry flags. -/
def spAdd (sp : UInt16) (e : UInt8) : UInt16 × Bool × Bool :=
  let base := sp.toNat
  let en := e.toNat
  let res := (((base : Int) + off8 e + 65536) % 65536).toNat
  let h := (base % 16) + (en % 16) > 15
  let c := (base % 256) + (en % 256) > 255
  (w16 res, h, c)

/-- Execute a decoded instruction at `fetchPC` (PC points at opcode).
    Returns updated state + total M-cycles. -/
def exec (s : GBState) (i : Instr) (fetchPC : UInt16) : GBState × Nat :=
  let r := s.regs
  let bug := s.haltBug
  -- Bugged fetch inhibits one PC increment, so immediates shift down
  -- by one byte (the repeated byte is re-read as the operand).
  let imm8 := busRead s (if bug then fetchPC else fetchPC + 1)
  let imm16 := read16 s (if bug then fetchPC else fetchPC + 1)
  -- default fall-through PC (adjusted for the HALT bug below)
  let bugAdj : UInt16 := if bug then 1 else 0
  let nextPC := fetchPC + w16 (Instr.len i) - bugAdj
  -- NOTE: `withPC` preserves `haltBug`; `stepCPU` clears it after exec.
  let withPC (st : GBState) (pc : UInt16) : GBState :=
    { st with regs := { st.regs with pc := pc } }
  match i with
  | .Nop => (withPC s nextPC, 1)
  | .Invalid => (withPC s nextPC, 1) -- v1 deviation: NOP instead of lockup
  | .Stop =>
    if s.cgb && s.speedPrep then
      -- KEY1 armed: switch CPU speed instead of halting
      -- (v1: the ~2 ms switch stall is not modelled)
      (withPC { s with doubleSpeed := !s.doubleSpeed, speedPrep := false }
        (fetchPC + 2), 1)
    else
      (withPC { s with regs := { r with halted := true } } (fetchPC + 2), 1)
  | .Halt =>
    let pending := irqPending s.ie s.if_
    if r.ime then
      let st := { s with regs := { r with halted := true }, haltBug := false }
      (withPC st (fetchPC + 1), 1)
    else match pending with
      | some _ =>
        if bug then
          -- double-halt spin: re-read this HALT forever, bug stays armed
          ({ s with regs := { r with pc := fetchPC }, haltBug := true }, 1)
        else
          let st := { s with regs := { r with pc := fetchPC + 1 }, haltBug := true }
          (st, 1)
      | none =>
        let st := { s with regs := { r with halted := true }, haltBug := false }
        (withPC st (fetchPC + 1), 1)
  | .Di => (withPC { s with regs := { r with ime := false, eiDelay := false } } nextPC, 1)
  | .Ei => (withPC { s with regs := { r with eiDelay := true } } nextPC, 1)
  | .Reti =>
    let (s1, v) := pop s
    (withPC { s1 with regs := { s1.regs with ime := true } } v, 4)
  | .Daa => (withPC (daa s) nextPC, 1)
  | .Cpl => (withPC { s with regs := { r with a := ~~~r.a, n := true, hf := true } } nextPC, 1)
  | .Scf => (withPC { s with regs := { r with n := false, hf := false, cf := true } } nextPC, 1)
  | .Ccf => (withPC { s with regs := { r with n := false, hf := false, cf := !r.cf } } nextPC, 1)
  | .Rlca =>
    let c := bitGet r.a 7
    let a := (r.a <<< 1) ||| (if c then 1 else 0)
    (withPC { s with regs := { r with a := a, z := false, n := false, hf := false, cf := c } } nextPC, 1)
  | .Rrca =>
    let c := bitGet r.a 0
    let a := (r.a >>> 1) ||| (if c then 0x80 else 0)
    (withPC { s with regs := { r with a := a, z := false, n := false, hf := false, cf := c } } nextPC, 1)
  | .Rla =>
    let c := bitGet r.a 7
    let a := (r.a <<< 1) ||| (if r.cf then 1 else 0)
    (withPC { s with regs := { r with a := a, z := false, n := false, hf := false, cf := c } } nextPC, 1)
  | .Rra =>
    let c := bitGet r.a 0
    let a := (r.a >>> 1) ||| (if r.cf then 0x80 else 0)
    (withPC { s with regs := { r with a := a, z := false, n := false, hf := false, cf := c } } nextPC, 1)
  | .LdR16Imm rr => (withPC (setR16 s rr imm16) nextPC, 3)
  | .LdMemR16BC => let (s1, c) := busWrite s r.bc r.a; (withPC s1 nextPC, 2 + c)
  | .LdMemR16DE => let (s1, c) := busWrite s r.de r.a; (withPC s1 nextPC, 2 + c)
  | .LdMemHLI =>
    let (s1, _) := busWrite s r.hl r.a
    let hl1 := r.hl + 1
    let st := { s1 with regs := { s1.regs with h := hiByte hl1, l := loByte hl1 } }
    (withPC st nextPC, 2)
  | .LdMemHLD =>
    let (s1, _) := busWrite s r.hl r.a
    let hl1 := r.hl - 1
    let st := { s1 with regs := { s1.regs with h := hiByte hl1, l := loByte hl1 } }
    (withPC st nextPC, 2)
  | .LdA_MemR16BC => (withPC { s with regs := { r with a := busRead s r.bc } } nextPC, 2)
  | .LdA_MemR16DE => (withPC { s with regs := { r with a := busRead s r.de } } nextPC, 2)
  | .LdA_MemHLI =>
    let a := busRead s r.hl
    (withPC { s with regs := { r with a := a, h := hiByte (r.hl + 1), l := loByte (r.hl + 1) } } nextPC, 2)
  | .LdA_MemHLD =>
    let a := busRead s r.hl
    (withPC { s with regs := { r with a := a, h := hiByte (r.hl - 1), l := loByte (r.hl - 1) } } nextPC, 2)
  | .IncR16 rr => (withPC (setR16 s rr (getR16 s rr + 1)) nextPC, 2)
  | .DecR16 rr => (withPC (setR16 s rr (getR16 s rr - 1)) nextPC, 2)
  | .AddHL rr =>
    let hl := r.hl
    let v := getR16 s rr
    let total := hl.toNat + v.toNat
    let h := ((hl.toNat % 4096) + (v.toNat % 4096)) >= 4096
    (withPC { s with regs := { (r.setHL (w16 (total % 65536))) with
      n := false, hf := h, cf := total > 0xFFFF } } nextPC, 2)
  | .IncR8 rr =>
    let x := getR8 s rr
    let v := x + 1
    let (s1, _) := setR8 s rr v
    let cy := if rr == .HLM then 3 else 1
    let st := { s1 with regs := { s1.regs with
      z := v == 0
      n := false
      hf := (x.toNat % 16) + 1 >= 16 } }
    (withPC st nextPC, cy)
  | .DecR8 rr =>
    let x := getR8 s rr
    let v := x - 1
    let (s1, _) := setR8 s rr v
    let cy := if rr == .HLM then 3 else 1
    let st := { s1 with regs := { s1.regs with
      z := v == 0
      n := true
      hf := (x.toNat % 16) == 0 } }
    (withPC st nextPC, cy)
  | .LdR8Imm rr =>
    let (s1, _) := setR8 s rr imm8
    (withPC s1 nextPC, if rr == .HLM then 3 else 2)
  | .LdRR dst src =>
    if dst == .HLM && src == .HLM then (withPC s nextPC, 1)
    else
      let v := getR8 s src
      let (s2, _) := setR8 s dst v
      let cy := if dst == .HLM || src == .HLM then 2 else 1
      (withPC s2 nextPC, cy)
  | .Jr none => (withPC s (pcRel nextPC imm8), 3)
  | .Jr (.some c) =>
    if condTrue s c then (withPC s (pcRel nextPC imm8), 3)
    else (withPC s nextPC, 2)
  | .Jp none => (withPC s imm16, 4)
  | .Jp (.some c) =>
    if condTrue s c then (withPC s imm16, 4) else (withPC s nextPC, 3)
  | .JpHL => (withPC s r.hl, 1)
  | .Call none =>
    let (s1, _) := push s nextPC
    (withPC s1 imm16, 6)
  | .Call (.some c) =>
    if condTrue s c then
      let (s1, _) := push s nextPC
      (withPC s1 imm16, 6)
    else (withPC s nextPC, 3)
  | .Ret none =>
    let (s1, v) := pop s
    (withPC s1 v, 4)
  | .Ret (.some c) =>
    if condTrue s c then
      let (s1, v) := pop s
      (withPC s1 v, 5)
    else (withPC s nextPC, 2)
  | .Rst k =>
    let (s1, _) := push s nextPC
    (withPC s1 (w16 (k * 8)), 4)
  | .Push rr =>
    let (s1, _) := push s (getRP s rr)
    (withPC s1 nextPC, 4)
  | .Pop rr =>
    let (s1, v) := pop s
    (withPC (setRP s1 rr v) nextPC, 3)
  | .AluImm op => (withPC (alu s op imm8) nextPC, 2)
  | .AluR op rr => (withPC (alu s op (getR8 s rr)) nextPC, if rr == .HLM then 2 else 1)
  | .LdMemNN_SP =>
    let (s1, c) := write16 s imm16 r.sp
    (withPC s1 nextPC, 5 + c)
  | .LdMemNN_A => let (s1, c) := busWrite s imm16 r.a; (withPC s1 nextPC, 4 + c)
  | .LdA_MemNN => (withPC { s with regs := { r with a := busRead s imm16 } } nextPC, 4)
  | .LdhMem_A =>
    let (s1, c) := busWrite s (w16 (0xFF00 + imm8.toNat)) r.a
    (withPC s1 nextPC, 3 + c)
  | .LdhA_Mem =>
    (withPC { s with regs := { r with a := busRead s (w16 (0xFF00 + imm8.toNat)) } } nextPC, 3)
  | .LdMemC_A => let (s1, c) := busWrite s (w16 (0xFF00 + r.c.toNat)) r.a; (withPC s1 nextPC, 2 + c)
  | .LdA_MemC =>
    (withPC { s with regs := { r with a := busRead s (w16 (0xFF00 + r.c.toNat)) } } nextPC, 2)
  | .AddSP =>
    let (res, h, c) := spAdd r.sp imm8
    let st := { s with regs := { r with sp := res, z := false, n := false, hf := h, cf := c } }
    (withPC st nextPC, 4)
  | .LdHL_SP =>
    let (res, h, c) := spAdd r.sp imm8
    let st := { s with regs := { (r.setHL res) with z := false, n := false, hf := h, cf := c } }
    (withPC st nextPC, 3)
  | .LdSP_HL => (withPC (setR16 s .SP r.hl) nextPC, 2)
  | .Rot op rr =>
    let (s1, _) := execCB s op rr
    (withPC s1 (fetchPC + 2 - bugAdj), if rr == .HLM then 4 else 2)
  | .Bit b rr =>
    let x := getR8 s rr
    let st := { s with regs := { r with z := !bitGet x b, n := false, hf := true } }
    (withPC st nextPC, if rr == .HLM then 3 else 2)
  | .Res b rr =>
    let (s1, _) := setR8 s rr (bitClear (getR8 s rr) b)
    (withPC s1 nextPC, if rr == .HLM then 4 else 2)
  | .Set b rr =>
    let (s1, _) := setR8 s rr (bitSet (getR8 s rr) b)
    (withPC s1 nextPC, if rr == .HLM then 4 else 2)

/-! ## Component stepping -/

/-- Finish a completed scanline: one HBlank-DMA block per visible line
    plus the framebuffer blit (DMG shades or CGB colors). -/
def finishLine (s : GBState) (ppu : PpuState) : GBState :=
  let done := (ppu.ly.toNat + 153) % 154
  if done < 144 then
    -- HBlank DMA transfers one block per visible scanline
    let s1 := hdmaHblank s
    let pr := { ppu with ly := w8 done }
    if s1.cgb then
      let line := PpuState.renderLineCgb pr s1.vram s1.oam s1.bgPal s1.obPal
      { s1 with fb := fbBlitColors s1.fb done line }
    else
      let line := PpuState.renderLine pr s1.vram s1.oam
      { s1 with fb := fbBlitLine s1.fb done line }
  else s

/-- Advance timer/serial/APU/PPU by `m` CPU M-cycles; collect IRQs
    into IF; run one HBlank-DMA block per completed visible scanline;
    render a completed scanline into the framebuffer.
    In double-speed mode 1 M-cycle = 2 T-cycles (else 4). -/
def advance (s : GBState) (m : Nat) : GBState :=
  let dots := if s.doubleSpeed then m * 2 else m * 4
  let timer := s.timer.stepDots dots
  let serial := s.serial.step dots
  let apu := s.apu.stepDots dots
  let (ppu, vblEdge, statEdge, lineDone, _frameDone) := s.ppu.step dots
  let mutIf := s.if_
  let mutIf := if timer.irq then irqRaise mutIf irqTimer else mutIf
  let mutIf := if serial.irq then irqRaise mutIf irqSerial else mutIf
  let mutIf := if vblEdge then irqRaise mutIf irqVBlank else mutIf
  let mutIf := if statEdge then irqRaise mutIf irqLCD else mutIf
  let timer := timer.ackIrq
  let serial := serial.ackIrq
  let ppu := ppu.ackVblank
  let s1 := { s with
    timer := timer
    serial := serial
    apu := apu
    ppu := ppu
    if_ := mutIf
    cycles := s.cycles + m }
  -- render the scanline that just completed (previous LY)
  if lineDone then finishLine s1 ppu else s1

/-- Service interrupt `bit`: push PC, jump to vector. -/
def serviceIrq (s : GBState) (bit : Nat) : GBState :=
  let (s1, _) := push s s.regs.pc
  let r := s1.regs
  let s2 := { s1 with
    regs := { r with pc := irqVector bit, ime := false, halted := false }
    if_ := irqAck s1.if_ bit }
  advance s2 5

/-- Execute a single CPU instruction (including HALT/interrupt logic). -/
def stepCPU (s : GBState) : GBState :=
  -- apply delayed EI
  let s := if s.regs.eiDelay then
    { s with regs := { s.regs with ime := true, eiDelay := false } } else s
  match irqPending s.ie s.if_ with
  | some bit =>
    if s.regs.ime then serviceIrq s bit
    else if s.regs.halted then
      -- wake without servicing
      advance { s with regs := { s.regs with halted := false } } 1
    else
      let pc := s.regs.pc
      let op := busRead s pc
      if op == 0xCB then
        let cb := busRead s (if s.haltBug then pc else pc + 1)
        let (s1, m) := exec s (Instr.decodeCB cb) pc
        advance { s1 with haltBug := false } m
      else
        let (s1, m) := exec s (Instr.decodeFull op) pc
        -- the HALT bug flag survives only a HALT instruction itself
        advance { s1 with haltBug := op == 0x76 && s1.haltBug } m
  | none =>
    if s.regs.halted then advance s 1
    else
      let pc := s.regs.pc
      let op := busRead s pc
      if op == 0xCB then
        let cb := busRead s (if s.haltBug then pc else pc + 1)
        let (s1, m) := exec s (Instr.decodeCB cb) pc
        advance { s1 with haltBug := false } m
      else
        let (s1, m) := exec s (Instr.decodeFull op) pc
        advance { s1 with haltBug := op == 0x76 && s1.haltBug } m

/-- Update the joypad from the frontend; edge presses raise IRQ + wake STOP. -/
def setButtons (s : GBState) (j : JoypadState) : GBState :=
  let was := s.joy.anyPressed
  let s1 := { s with joy := j }
  -- STOP wakes on any button press
  let s2 := if j.anyPressed then
    { s1 with regs := { s1.regs with halted := false } } else s1
  if j.anyPressed && !was then
    { s2 with if_ := irqRaise s2.if_ irqJoypad }
  else s2

end GB
