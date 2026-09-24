/-
  LeanAGB.Bus — AGBState (pure), GBA memory map, Thumb executor,
  HLE SWI dispatch, IRQ entry, cycle advance (timers + PPU counter).
-/
import LeanAGB.Basic
import LeanAGB.Cpu.Regs
import LeanAGB.Cpu.Decode
import LeanAGB.Apu
import LeanAGB.Timer
import LeanAGB.Irq
import LeanAGB.Dma
import LeanAGB.Keypad
import LeanAGB.Ppu
import LeanAGB.Bios
import LeanAGB.Cartridge.Save

namespace AGB

/-- Full GBA state. Pure: every step is `AGBState → AGBState`. -/
structure AGBState where
  regs : ArmRegs := {}
  ewram : ByteArray := ByteArray.empty
  iwram : ByteArray := ByteArray.empty
  pal : ByteArray := ByteArray.empty
  vram : ByteArray := ByteArray.empty
  oam : ByteArray := ByteArray.empty
  io : ByteArray := ByteArray.empty
  rom : ByteArray := ByteArray.empty
  save : SaveState := {}
  irq : AgbIrq := {}
  timers : AgbTimers := {}
  dma : AgbDma := {}
  key : AgbKeypad := {}
  ppu : AgbPpu := {}
  fb : Array UInt32 := Array.replicate 38400 (0xFFFFFFFF : UInt32)
  cycles : Nat := 0
  halted : Bool := false
  /-- Last prefetched word (open-bus source; latched on fetch). -/
  busVal : UInt32 := 0
  /-- IntrWait/VBlankWait wake mask (0 = any enabled IRQ; set by HLE SWI). -/
  waitMask : UInt16 := 0
  /-- Embedded minimal BIOS (IRQ dispatcher stub; rest zeros). -/
  bios : ByteArray := ByteArray.empty
  /-- Sound (PSG + DMA FIFOs + mixer; stepped with `advance`). -/
  apu : AgbApu := {}

/-- Fresh state with a chosen backup medium. -/
def AGBState.freshSave (rom : ByteArray) (kind : SaveKind) : AGBState :=
  let blank (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n (0 : UInt8))
  { regs := { r := ((Array.replicate 16 (0 : UInt32)).set! 15 0x08000000).set! 13 0x03007F00,
              cpsr := 0x3F,  -- SYS mode + T bit (direct-boot Thumb)
              r13_svc := 0x03007FE0, r13_irq := 0x03007FA0 }
    ewram := blank 0x40000, iwram := blank 0x8000,
    pal := blank 0x400, vram := blank 0x18000, oam := blank 0x400,
    io := blank 0x400, rom := rom, save := SaveState.fresh kind, bios := agbBios }

/-- Fresh state: sizes per HW, direct-boot to ROM with Thumb set. -/
def AGBState.fresh (rom : ByteArray) : AGBState :=
  AGBState.freshSave rom .sram

/-- Fresh state for commercial ROMs: same layout, but ARM state —
    real carts start with an ARM branch over the Nintendo logo
    (Thumb boot would slide off into address 0 within microcycles). -/
def AGBState.freshArmSave (rom : ByteArray) (kind : SaveKind) : AGBState :=
  let s := AGBState.freshSave rom kind
  { s with regs := { s.regs with cpsr := 0x1F } }

/-- ARM-state boot iff the ROM entry looks like an ARM branch (`B`/`BL`:
    bits 27–25 = `101`). Real carts start with an ARM `B` over the logo;
    Thumb homebrew does not. Empty/short ROMs read 0xFF (open bus) → Thumb. -/
def bootIsArm (rom : ByteArray) : Bool :=
  ((bget32LE rom 0).toNat >>> 25) &&& 0x7 == 0b101

/-- Fresh state with per-ROM boot-state detection (ARM for commercial
    carts, Thumb otherwise). -/
def AGBState.freshAuto (rom : ByteArray) (kind : SaveKind) : AGBState :=
  if bootIsArm rom then AGBState.freshArmSave rom kind
  else AGBState.freshSave rom kind

/-- Reset-vector state for a real-BIOS boot (`--bios gba_bios.bin`):
    ARM state, SVC mode with I+F masked (ARM reset: CPSR = 0xD3),
    PC = 0x00000000, stacks installed by `freshSave`
    (SP_sys = 0x03007F00, SP_svc = 0x03007FE0, SP_irq = 0x03007FA0).
    `bios` is padded/truncated to the 16 KiB BIOS window (0x0000-0x3FFF).
    The BIOS runs its logo check + intro, then jumps to the ROM entry —
    which is exactly what a TAS recorded with `SkipBios = false` needs. -/
def AGBState.freshBiosBoot (rom bios : ByteArray) (kind : SaveKind) : AGBState :=
  let s := AGBState.freshSave rom kind
  let padded :=
    if bios.size == 0x4000 then bios
    else if bios.size > 0x4000 then bios.extract 0 0x4000
    else bios ++ ByteArray.mk (Array.replicate (0x4000 - bios.size) (0 : UInt8))
  let s := { s with bios := padded }
  { s with regs := { s.regs with cpsr := 0xD3, r := s.regs.r.set! 15 0 } }

/-- ROM base address (direct-boot PC). -/
def ROM_BASE : Nat := 0x08000000

-- ── Memory map (mirrors per gbadoc; open bus from last prefetch) ──

/-- ROM window read: blob mirrored modulo size (WS0/1/2 share the chip). -/
def romMirror (s : AGBState) (a : Nat) : UInt8 :=
  if s.rom.size == 0 then openBus8 s.busVal a
  else bget s.rom ((a - 0x08000000) % s.rom.size)

/-- 0x0E-window byte read by backup kind (EEPROM carts: open bus here). -/
def saveRead8 (s : AGBState) (off : Nat) : UInt8 :=
  match s.save.kind with
  | .sram => bget s.save.sram off
  | .flash64 => flashRead s.save.flash false off
  | .flash128 => flashRead s.save.flash true off
  | _ => openBus8 s.busVal (0x0E000000 + off)

/-- 0x0E-window byte write by backup kind (EEPROM carts: ignored here). -/
def saveWrite8 (s : AGBState) (off : Nat) (v : UInt8) : AGBState :=
  match s.save.kind with
  | .sram => { s with save := { s.save with sram := bset s.save.sram off v } }
  | .flash64 => { s with save := { s.save with flash := flashWrite s.save.flash false off v } }
  | .flash128 => { s with save := { s.save with flash := flashWrite s.save.flash true off v } }
  | _ => s

/-- Live 16-bit IO read helpers (Phase 0: structs are source of truth). -/
def dispstatLive (s : AGBState) : UInt16 := s.ppu.dispstat
def vcountLive (s : AGBState) : UInt16 := s.ppu.vcount
def timerCntLive (s : AGBState) (ch : Nat) : UInt16 :=
  (s.timers.ch.getD ch {}).cnt
/-- Live DMA CNT_H byte (R/W on HW; enable clears on completion, so
    reads must see the struct, not the write shadow — a stale shadow
    hangs completion-polling games). SAD/DAD/CNT_L stay shadowed. -/
def dmaCntHLive (s : AGBState) (ch : Nat) (hi : Bool) : UInt8 :=
  let h := (s.dma.ch.getD ch {}).cnt_h
  if hi then ((h >>> 8) &&& 0xFF).toUInt8 else (h &&& 0xFF).toUInt8

/-- Live BG register bytes (BG0-3CNT + scroll offsets). -/
def bgRead8Live (s : AGBState) (a : Nat) : Option UInt8 :=
  if 0x04000008 <= a && a <= 0x0400000F then
    let v := s.ppu.bgcnt.getD ((a - 0x04000008) / 2) 0
    some (if a % 2 == 0 then (v &&& 0xFF).toUInt8 else ((v >>> 8) &&& 0xFF).toUInt8)
  else if 0x04000010 <= a && a <= 0x0400001F then
    let ch := (a - 0x04000010) / 4
    let v := if ((a - 0x04000010) % 4) < 2 then s.ppu.bghofs.getD ch 0
             else s.ppu.bgvofs.getD ch 0
    some (if a % 2 == 0 then (v &&& 0xFF).toUInt8 else ((v >>> 8) &&& 0xFF).toUInt8)
  else none

def ioRead8Live (s : AGBState) (a : Nat) : Option UInt8 :=
  if a == 0x04000000 then some (s.ppu.dispcnt &&& 0xFF).toUInt8
  else if a == 0x04000001 then some ((s.ppu.dispcnt >>> 8) &&& 0xFF).toUInt8
  else if 0x04000008 <= a && a <= 0x0400001F then bgRead8Live s a
  else if a == 0x040000BA then some (dmaCntHLive s 0 false)
  else if a == 0x040000BB then some (dmaCntHLive s 0 true)
  else if a == 0x040000C6 then some (dmaCntHLive s 1 false)
  else if a == 0x040000C7 then some (dmaCntHLive s 1 true)
  else if a == 0x040000D2 then some (dmaCntHLive s 2 false)
  else if a == 0x040000D3 then some (dmaCntHLive s 2 true)
  else if a == 0x040000DE then some (dmaCntHLive s 3 false)
  else if a == 0x040000DF then some (dmaCntHLive s 3 true)
  else if a == 0x04000004 then some (dispstatLive s &&& 0xFF).toUInt8
  else if a == 0x04000005 then some (((dispstatLive s) >>> 8) &&& 0xFF).toUInt8
  else if a == 0x04000006 then some (vcountLive s &&& 0xFF).toUInt8
  else if a == 0x04000007 then some (((vcountLive s) >>> 8) &&& 0xFF).toUInt8
  else if a == 0x04000100 then some (timerCntLive s 0 &&& 0xFF).toUInt8
  else if a == 0x04000101 then some (((timerCntLive s 0) >>> 8) &&& 0xFF).toUInt8
  else if a == 0x04000104 then some (timerCntLive s 1 &&& 0xFF).toUInt8
  else if a == 0x04000105 then some (((timerCntLive s 1) >>> 8) &&& 0xFF).toUInt8
  else if a == 0x04000108 then some (timerCntLive s 2 &&& 0xFF).toUInt8
  else if a == 0x04000109 then some (((timerCntLive s 2) >>> 8) &&& 0xFF).toUInt8
  else if a == 0x0400010C then some (timerCntLive s 3 &&& 0xFF).toUInt8
  else if a == 0x0400010D then some (((timerCntLive s 3) >>> 8) &&& 0xFF).toUInt8
  else if a == 0x04000130 then some (s.key.input &&& 0xFF).toUInt8
  else if a == 0x04000131 then some ((s.key.input >>> 8) &&& 0xFF).toUInt8
  else if a == 0x04000132 then some (s.key.cnt &&& 0xFF).toUInt8
  else if a == 0x04000133 then some (((s.key.cnt) >>> 8) &&& 0xFF).toUInt8
  else if a == 0x04000200 then some (s.irq.ie &&& 0xFF).toUInt8
  else if a == 0x04000201 then some (((s.irq.ie) >>> 8) &&& 0xFF).toUInt8
  else if a == 0x04000202 then some (s.irq.if_ &&& 0xFF).toUInt8
  else if a == 0x04000203 then some (((s.irq.if_) >>> 8) &&& 0xFF).toUInt8
  else if a == 0x04000208 then some (if s.irq.ime then 1 else 0)
  else if a == 0x04000300 then some 0  -- POSTFLG stub
  else if 0x04000090 <= a && a < 0x040000A0 then
    -- wave RAM: CPU sees the non-playing bank (GBATEK wave page)
    some (apuWaveRead s.apu (a - 0x04000090))
  else if a == 0x04000084 then some (apuStatus s.apu &&& 0xFF).toUInt8
  else if a == 0x04000085 then some (((apuStatus s.apu) >>> 8) &&& 0xFF).toUInt8
  else none

def memRead8 (s : AGBState) (addr : UInt32) : UInt8 :=
  let a := addr.toNat
  if a < 0x4000 then bget s.bios a
  else if 0x02000000 <= a && a < 0x03000000 then
    bget s.ewram (mirrorIdx 0x02000000 0x40000 a)
  else if 0x03000000 <= a && a < 0x04000000 then
    bget s.iwram (mirrorIdx 0x03000000 0x8000 a)
  else if 0x04000000 <= a && a < 0x05000000 then
    match ioRead8Live s a with
    | some v => v
    | none => bget s.io (a - 0x04000000)
  else if 0x05000000 <= a && a < 0x06000000 then
    bget s.pal (mirrorIdx 0x05000000 0x400 a)
  else if 0x06000000 <= a && a < 0x07000000 then bget s.vram (vramIdx a)
  else if 0x07000000 <= a && a < 0x08000000 then
    bget s.oam (mirrorIdx 0x07000000 0x400 a)
  else if 0x08000000 <= a && a < 0x0E000000 then
    if (s.save.kind == .eeprom4k || s.save.kind == .eeprom64k) && 0x0D000000 <= a then
      -- EEPROM window peek for non-instruction paths (fetch/DMA/BIOS);
      -- game loads use memRead*E which clock the protocol.
      openBus8 s.busVal a
    else romMirror s a
  else if 0x0E000000 <= a && a < 0x10000000 then
    saveRead8 s ((a - 0x0E000000) % 0x10000)
  else openBus8 s.busVal a

def memRead16 (s : AGBState) (addr : UInt32) : UInt16 :=
  let lo := (memRead8 s addr).toUInt16
  let hi := (memRead8 s (addr + 1)).toUInt16
  (hi <<< 8) ||| lo

def memRead32 (s : AGBState) (addr : UInt32) : UInt32 :=
  let b0 := (memRead8 s addr).toUInt32
  let b1 := (memRead8 s (addr + 1)).toUInt32
  let b2 := (memRead8 s (addr + 2)).toUInt32
  let b3 := (memRead8 s (addr + 3)).toUInt32
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)

-- ── Serial-window reads (Phase 6: EEPROM) ──
-- Game LDR-family loads use these stateful versions so the EEPROM bit
-- protocol clocks on every window access (writes already thread state).
-- Fetch, block transfers, DMA and BIOS bulk readers keep the pure path:
-- the serial window is meaningless for those (each access is one bit),
-- and their addresses never legitimately land there.

/-- Stateful byte read: EEPROM window clocks `eepromReadBit`
    (D0 carries data, upper bits stay open bus). -/
def memRead8E (s : AGBState) (addr : UInt32) : AGBState × UInt8 :=
  let a := addr.toNat
  if (s.save.kind == .eeprom4k || s.save.kind == .eeprom64k)
      && 0x0D000000 <= a && a < 0x0E000000 then
    let (e, bit) := eepromReadBit s.save.eeprom
    let s := { s with save := { s.save with eeprom := e } }
    (s, ((openBus8 s.busVal a) &&& (0xFE : UInt8))
      ||| (if bit then (1 : UInt8) else (0 : UInt8)))
  else (s, memRead8 s addr)

def memRead16E (s : AGBState) (addr : UInt32) : AGBState × UInt16 :=
  let (s, lo) := memRead8E s addr
  let (s, hi) := memRead8E s (addr + 1)
  (s, (hi.toUInt16 <<< 8) ||| lo.toUInt16)

def memRead32E (s : AGBState) (addr : UInt32) : AGBState × UInt32 :=
  let (s, b0) := memRead8E s addr
  let (s, b1) := memRead8E s (addr + 1)
  let (s, b2) := memRead8E s (addr + 2)
  let (s, b3) := memRead8E s (addr + 3)
  (s, b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16)
    ||| (b3.toUInt32 <<< 24))

/-- Byte-lane helpers for IO struct sync. -/
def putLo8 (x : UInt16) (b : UInt8) : UInt16 :=
  (x &&& (0xFF00 : UInt16)) ||| b.toUInt16
def putHi8 (x : UInt16) (b : UInt8) : UInt16 :=
  (x &&& (0x00FF : UInt16)) ||| (b.toUInt16 <<< 8)
def put32Lo16 (x : UInt32) (v : UInt16) : UInt32 :=
  (x &&& (0xFFFF0000 : UInt32)) ||| v.toUInt32
def put32Hi16 (x : UInt32) (v : UInt16) : UInt32 :=
  (x &&& (0x0000FFFF : UInt32)) ||| (v.toUInt32 <<< 16)

/-- Timer reload lane: stores the reload value (the live counter is
    untouched — GBATEK: reload copies on overflow or start-bit edge). -/
def syncTimerReload (s : AGBState) (i : Nat) (v : UInt16) : AGBState :=
  let ch := s.timers.ch.getD i {}
  { s with timers := { ch := s.timers.ch.set! i { ch with reload := v } } }

/-- Timer control lane: stores ctrl, and on start-bit rising edge
    (0→1) copies reload into the counter (GBATEK timer page). -/
def syncTimerCtrl (s : AGBState) (i : Nat) (v : UInt16) : AGBState :=
  let ch := s.timers.ch.getD i {}
  let oldEn := ((ch.ctrl >>> 7) &&& 1) == 1
  let newEn := ((v >>> 7) &&& 1) == 1
  let ch := { ch with ctrl := v }
  let ch := if !oldEn && newEn then { ch with cnt := ch.reload } else ch
  { s with timers := { ch := s.timers.ch.set! i ch } }

def syncTimer16 (s : AGBState) (a : Nat) (v : UInt16) : AGBState :=
  if a == 0x04000100 then syncTimerReload s 0 v
  else if a == 0x04000102 then syncTimerCtrl s 0 v
  else if a == 0x04000104 then syncTimerReload s 1 v
  else if a == 0x04000106 then syncTimerCtrl s 1 v
  else if a == 0x04000108 then syncTimerReload s 2 v
  else if a == 0x0400010A then syncTimerCtrl s 2 v
  else if a == 0x0400010C then syncTimerReload s 3 v
  else if a == 0x0400010E then syncTimerCtrl s 3 v
  else s

/-- Update one DMA channel's 16-bit lane (SAD/DAD halves, CNT_L/CNT_H). -/
def syncDmaCh (s : AGBState) (idx base a : Nat) (v : UInt16) : AGBState :=
  if a == base then
    let d := s.dma.ch.getD idx {}
    { s with dma := { ch := s.dma.ch.set! idx { d with sad := put32Lo16 d.sad v } } }
  else if a == base + 2 then
    let d := s.dma.ch.getD idx {}
    { s with dma := { ch := s.dma.ch.set! idx { d with sad := put32Hi16 d.sad v } } }
  else if a == base + 4 then
    let d := s.dma.ch.getD idx {}
    { s with dma := { ch := s.dma.ch.set! idx { d with dad := put32Lo16 d.dad v } } }
  else if a == base + 6 then
    let d := s.dma.ch.getD idx {}
    { s with dma := { ch := s.dma.ch.set! idx { d with dad := put32Hi16 d.dad v } } }
  else if a == base + 8 then
    let d := s.dma.ch.getD idx {}
    { s with dma := { ch := s.dma.ch.set! idx { d with cnt_l := v } } }
  else if a == base + 10 then
    let d := s.dma.ch.getD idx {}
    { s with dma := { ch := s.dma.ch.set! idx { d with cnt_h := v } } }
  else s

/-- Update one DMA 16-bit lane (SAD/DAD halves, CNT_L/CNT_H). -/
def syncDma16 (s : AGBState) (a : Nat) (v : UInt16) : AGBState :=
  syncDmaCh (syncDmaCh (syncDmaCh (syncDmaCh s 0 0x040000B0 a v) 1 0x040000BC a v) 2 0x040000C8 a v) 3 0x040000D4 a v

/-- Sound register sync (PSG lanes 0x60-0x88; wave RAM 0x90+ and FIFO
    0xA0+ take explicit byte/word branches instead — FIFO pushes and
    banked wave writes can't go through lane merging). -/
def syncApu16 (s : AGBState) (a : Nat) (v : UInt16) : AGBState :=
  if 0x04000060 <= a && a <= 0x04000088 then
    { s with apu := apuWrite16 s.apu a v }
  else s

/-- Total 4-lane update (length-preserving by construction, unlike
    `set!` which is stuck on short arrays and defeats readback proofs). -/
def setLane4 (a : Array UInt16) (i : Nat) (v : UInt16) : Array UInt16 :=
  if i == 0 then #[v, a.getD 1 0, a.getD 2 0, a.getD 3 0]
  else if i == 1 then #[a.getD 0 0, v, a.getD 2 0, a.getD 3 0]
  else if i == 2 then #[a.getD 0 0, a.getD 1 0, v, a.getD 3 0]
  else #[a.getD 0 0, a.getD 1 0, a.getD 2 0, v]

/-- BG layer register sync, split for the `split` tactic budget:
    BG0-3CNT (0x08-0x0E), HOFS (0x10/14/18/1C), VOFS (0x12/16/1A/1E).
    Palette/VRAM/OAM have no structs. -/
def syncBgCnt (s : AGBState) (a : Nat) (v : UInt16) : AGBState :=
  if a == 0x04000008 then
    { s with ppu := { s.ppu with bgcnt := setLane4 s.ppu.bgcnt 0 v } }
  else if a == 0x0400000A then
    { s with ppu := { s.ppu with bgcnt := setLane4 s.ppu.bgcnt 1 v } }
  else if a == 0x0400000C then
    { s with ppu := { s.ppu with bgcnt := setLane4 s.ppu.bgcnt 2 v } }
  else if a == 0x0400000E then
    { s with ppu := { s.ppu with bgcnt := setLane4 s.ppu.bgcnt 3 v } }
  else s

def syncBgHo (s : AGBState) (a : Nat) (v : UInt16) : AGBState :=
  if a == 0x04000010 then
    { s with ppu := { s.ppu with bghofs := setLane4 s.ppu.bghofs 0 v } }
  else if a == 0x04000014 then
    { s with ppu := { s.ppu with bghofs := setLane4 s.ppu.bghofs 1 v } }
  else if a == 0x04000018 then
    { s with ppu := { s.ppu with bghofs := setLane4 s.ppu.bghofs 2 v } }
  else if a == 0x0400001C then
    { s with ppu := { s.ppu with bghofs := setLane4 s.ppu.bghofs 3 v } }
  else s

def syncBgVo (s : AGBState) (a : Nat) (v : UInt16) : AGBState :=
  if a == 0x04000012 then
    { s with ppu := { s.ppu with bgvofs := setLane4 s.ppu.bgvofs 0 v } }
  else if a == 0x04000016 then
    { s with ppu := { s.ppu with bgvofs := setLane4 s.ppu.bgvofs 1 v } }
  else if a == 0x0400001A then
    { s with ppu := { s.ppu with bgvofs := setLane4 s.ppu.bgvofs 2 v } }
  else if a == 0x0400001E then
    { s with ppu := { s.ppu with bgvofs := setLane4 s.ppu.bgvofs 3 v } }
  else s

/-- Color-effect register sync: BLDCNT/BLDALPHA/BLDY. -/
def syncBld16 (s : AGBState) (a : Nat) (v : UInt16) : AGBState :=
  if a == 0x04000050 then
    { s with ppu := { s.ppu with bldcnt := v } }
  else if a == 0x04000052 then
    { s with ppu := { s.ppu with bldalpha := v } }
  else if a == 0x04000054 then
    { s with ppu := { s.ppu with bldy := v } }
  else s

def syncBg16 (s : AGBState) (a : Nat) (v : UInt16) : AGBState :=
  syncBgVo (syncBgHo (syncBgCnt s a v) a v) a v

/-- 16-bit IO struct sync: PPU/timers/DMA/keypad (IRQ handled by
    caller). Immediate-DMA firing lives at the `memWrite16` CNT_H
    branches instead, keeping every helper non-recursive. -/
def syncIo16 (s : AGBState) (a : Nat) (v : UInt16) : AGBState :=
  let s := if a == 0x04000000 then
      { s with ppu := { s.ppu with dispcnt := v } }
    else if a == 0x04000004 then
      -- DISPSTAT: RO flags 0-2 preserved; RW = bits 3-5 + 8-15
      let old := s.ppu.dispstat
      let lo : UInt16 := ((old &&& (0xFF : UInt16)) &&& ~~~(0x38 : UInt16))
        ||| (((v &&& (0xFF : UInt16)) &&& (0x38 : UInt16)))
      let hi : UInt16 := ((v >>> 8) &&& (0xFF : UInt16))
      { s with ppu := { s.ppu with dispstat := (lo &&& (0xFF : UInt16)) ||| (hi <<< 8) } }
    else if a == 0x04000132 then { s with key := { s.key with cnt := v } }
    else s
  let s := syncTimer16 s a v
  let s := syncDma16 s a v
  let s := syncApu16 s a v
  let s := syncBg16 s a v
  syncBld16 s a v
-- ── DMA engine (Phase 1; IO sync added Phase 9) ──
-- Copies use `dmaWrite*` instead of `memWrite*` so the call chain stays
-- acyclic: sync helpers never fire DMA; only `memWrite16` CNT_H lanes
-- call `fireDmaCh`, and `dmaWrite` never triggers nested transfers.

/-- Wrapping `UInt32 + Int` (address stepping; HW wraps mod 2^32). -/
def addW32 (a : UInt32) (d : Int) : UInt32 :=
  w32 ((((a.toNat : Int) + d).emod 0x100000000).toNat)

/-- Push one byte into FIFO `w` (0 = A at 0x040000A0, 1 = B at 0xA4). -/
def apuFifoPush (s : AGBState) (w : Nat) (v : UInt8) : AGBState :=
  if w == 0 then { s with apu := { s.apu with fifoA := fifoPush s.apu.fifoA v } }
  else { s with apu := { s.apu with fifoB := fifoPush s.apu.fifoB v } }

/-- DMA completion IRQ bit: DMA0 → IF.8 … DMA3 → IF.11. -/
def dmaIrqBit : Nat → UInt16
  | 0 => 0x0100 | 1 => 0x0200 | 2 => 0x0400 | _ => 0x0800

/-- DMA IO-range byte write (FIFO push / banked wave / shadow sync).
    Split out so no dispatch chain exceeds the old `split` budget. -/
def dmaWrite8IO (s : AGBState) (a : Nat) (v : UInt8) : AGBState :=
  if 0x040000A0 <= a && a < 0x040000A8 then
    apuFifoPush s ((a - 0x040000A0) / 4) v
  else if 0x04000090 <= a && a < 0x040000A0 then
    { s with apu := apuWaveWrite s.apu (a - 0x04000090) v }
  else
    let io := bset s.io (a - 0x04000000) v
    let s := { s with io := io }
    if a == 0x04000208 then { s with irq := { s.irq with ime := (v.toNat &&& 1) == 1 } }
    else
      let lane := a - (a % 2)
      syncIo16 s lane (bget16LE s.io (lane - 0x04000000))

/-- DMA byte write by raw address (worker: no `let`, so `split` sees
    the dispatch chain directly). -/
def dmaWrite8Nat (s : AGBState) (a : Nat) (v : UInt8) : AGBState :=
  if 0x02000000 <= a && a < 0x03000000 then
    { s with ewram := bset s.ewram (mirrorIdx 0x02000000 0x40000 a) v }
  else if 0x03000000 <= a && a < 0x04000000 then
    { s with iwram := bset s.iwram (mirrorIdx 0x03000000 0x8000 a) v }
  else if 0x04000000 <= a && a < 0x05000000 then dmaWrite8IO s a v
  else if 0x05000000 <= a && a < 0x06000000 then
    { s with pal := bset s.pal (mirrorIdx 0x05000000 0x400 a) v }
  else if 0x06000000 <= a && a < 0x07000000 then
    { s with vram := bset s.vram (vramIdx a) v }
  else if 0x07000000 <= a && a < 0x08000000 then
    { s with oam := bset s.oam (mirrorIdx 0x07000000 0x400 a) v }
  else if 0x0E000000 <= a && a < 0x10000000 then
    saveWrite8 s ((a - 0x0E000000) % 0x10000) v
  else s

/-- DMA byte write: RAM/VRAM/PAL/OAM raw, IO shadow + struct sync
    (bulk writes never fire nested DMA), ROM dropped. -/
def dmaWrite8 (s : AGBState) (addr : UInt32) (v : UInt8) : AGBState :=
  dmaWrite8Nat s addr.toNat v

def dmaWrite16 (s : AGBState) (addr : UInt32) (v : UInt16) : AGBState :=
  dmaWrite8 (dmaWrite8 s addr v.toUInt8) (addr + 1) (v >>> 8).toUInt8

def dmaWrite32 (s : AGBState) (addr : UInt32) (v : UInt32) : AGBState :=
  dmaWrite16 (dmaWrite16 s addr v.toUInt16) (addr + 2) (v >>> 16).toUInt16

/-- One DMA unit transfer (reads via live `memRead`, writes via `dmaWrite`). -/
def dmaStep (s : AGBState) (src dst : UInt32) (is32 : Bool) : AGBState :=
  if is32 then dmaWrite32 s dst (memRead32 s src)
  else dmaWrite16 s dst (memRead16 s src)

/-- DMA copy loop (`fuel` = word count; byte-deltas precomputed). -/
def dmaCopy : AGBState → UInt32 → UInt32 → Nat → Bool → Int → Int → AGBState
  | s, _, _, 0, _, _, _ => s
  | s, src, dst, fuel + 1, is32, sstep, dstep =>
    dmaCopy (dmaStep s src dst is32) (addW32 src sstep) (addW32 dst dstep) fuel is32 sstep dstep

/-- Raw backing store for DMA bulk (no per-byte struct side effects). -/
inductive DmaRaw where
  | ew | iw | pal | vram | oam
deriving DecidableEq, Repr

/-- Bulk source tag (ROM never overlaps a raw dest). -/
inductive DmaSrc where
  | ew | iw | rom
deriving DecidableEq, Repr

/-- Linear source window: tag + bytes + offset, or none (mirror wrap,
    EEPROM serial window, IO/save/open-bus → slow path). Reads are pure,
    so any linear window is an exact slice of the pre-transfer state. -/
def dmaLinSrc (s : AGBState) (a total : Nat) : Option (DmaSrc × ByteArray × Nat) :=
  if 0x02000000 <= a && a < 0x03000000 && (a - 0x02000000) + total <= 0x40000 then
    some (.ew, s.ewram, (a - 0x02000000) % 0x40000)
  else if 0x03000000 <= a && a < 0x04000000 && (a - 0x03000000) + total <= 0x8000 then
    some (.iw, s.iwram, (a - 0x03000000) % 0x8000)
  else if 0x08000000 <= a && a < 0x0E000000 && s.rom.size != 0
      && !((s.save.kind == .eeprom4k || s.save.kind == .eeprom64k) && 0x0D000000 <= a)
      && (a - 0x08000000) + total <= s.rom.size then
    some (.rom, s.rom, a - 0x08000000)
  else none

/-- Linear dest window: store + offset, or none (IO/FIFO/wave/sync lanes,
    save/flash/EEPROM, ROM/other → slow path). -/
def dmaLinDst (a total : Nat) : Option (DmaRaw × Nat) :=
  if 0x02000000 <= a && a < 0x03000000 && (a - 0x02000000) + total <= 0x40000 then
    some (.ew, (a - 0x02000000) % 0x40000)
  else if 0x03000000 <= a && a < 0x04000000 && (a - 0x03000000) + total <= 0x8000 then
    some (.iw, (a - 0x03000000) % 0x8000)
  else if 0x05000000 <= a && a < 0x06000000 && (a - 0x05000000) + total <= 0x400 then
    some (.pal, (a - 0x05000000) % 0x400)
  else if 0x06000000 <= a && a < 0x07000000 then
    let i := (a - 0x06000000) % 0x20000
    if i + total <= 0x18000 then some (.vram, i)
    else if 0x18000 <= i && i + total <= 0x20000 then some (.vram, i - 0x8000)
    else none
  else if 0x07000000 <= a && a < 0x08000000 && (a - 0x07000000) + total <= 0x400 then
    some (.oam, (a - 0x07000000) % 0x400)
  else none

/-- Half-open range intersection (empty ranges never overlap). -/
def rangesOverlap (o1 o2 total : Nat) : Bool :=
  o1 < o2 + total && o2 < o1 + total

/-- Bulk byte copy for increment-increment DMA over linear windows.
    Returns none (caller falls back to `dmaCopy`) on any nonlinearity,
    same-store overlap (slow path order matters there), or
    side-effecting region. One state commit instead of ~4 allocs/byte. -/
def dmaBulk (s : AGBState) (src dst : UInt32) (total : Nat) : Option AGBState :=
  match dmaLinSrc s src.toNat total, dmaLinDst dst.toNat total with
  | some (.ew, sarr, soff), some (.ew, doff) =>
    if rangesOverlap soff doff total then none
    else some { s with ewram := sarr.copySlice soff s.ewram doff total }
  | some (.iw, sarr, soff), some (.iw, doff) =>
    if rangesOverlap soff doff total then none
    else some { s with iwram := sarr.copySlice soff s.iwram doff total }
  | some (_, sarr, soff), some (.ew, doff) =>
    some { s with ewram := sarr.copySlice soff s.ewram doff total }
  | some (_, sarr, soff), some (.iw, doff) =>
    some { s with iwram := sarr.copySlice soff s.iwram doff total }
  | some (_, sarr, soff), some (.pal, doff) =>
    some { s with pal := sarr.copySlice soff s.pal doff total }
  | some (_, sarr, soff), some (.vram, doff) =>
    some { s with vram := sarr.copySlice soff s.vram doff total }
  | some (_, sarr, soff), some (.oam, doff) =>
    some { s with oam := sarr.copySlice soff s.oam doff total }
  | _, _ => none

/-- Copy dispatch: bulk slice when increment-increment over linear
    windows, else the exact word-by-word loop. -/
def dmaRun (s : AGBState) (src dst : UInt32) (count : Nat) (is32 : Bool)
    (sstep dstep : Int) (unit : Nat) : AGBState :=
  if sstep == (unit : Int) && dstep == (unit : Int) then
    match dmaBulk s src dst (count * unit) with
    | some s1 => s1
    | none => dmaCopy s src dst count is32 sstep dstep
  else dmaCopy s src dst count is32 sstep dstep

/-- Run channel `ch` to completion now (SAD/DAD stepping, repeat/IRQ). -/
def doDma (s : AGBState) (ch : Nat) : AGBState :=
  let d := s.dma.ch.getD ch {}
  let timing := (d.cnt_h.toNat >>> 12) &&& 0x3
  let rep := ((d.cnt_h >>> 9) &&& 1) == 1
  let irqEn := ((d.cnt_h >>> 14) &&& 1) == 1
  let is32 := ((d.cnt_h >>> 10) &&& 1) == 1
  let unit : Nat := if is32 then 4 else 2
  let c0 := d.cnt_l.toNat
  let count := if c0 == 0 then (if ch == 3 then 0x10000 else 0x4000) else c0
  let dstC := (d.cnt_h.toNat >>> 5) &&& 0x3
  let srcC := (d.cnt_h.toNat >>> 7) &&& 0x3
  let sstep : Int := if srcC == 1 then -((unit : Int)) else if srcC == 2 then 0 else unit
  let dstep : Int := if dstC == 1 then -((unit : Int)) else if dstC == 2 then 0 else unit
  let s1 := dmaRun s d.sad d.dad count is32 sstep dstep unit
  let sadEnd := addW32 d.sad ((count : Int) * sstep)
  -- dest reload (11) restores the start address (sound-FIFO shape)
  let dadEnd := if dstC == 3 then d.dad else addW32 d.dad ((count : Int) * dstep)
  -- repeat only survives on non-immediate timings; immediate always clears
  let keepEn := rep && timing != 0
  let newH := if keepEn then d.cnt_h else d.cnt_h &&& (0x7FFF : UInt16)
  let d2 := { d with sad := sadEnd, dad := dadEnd, cnt_h := newH }
  let s2 := { s1 with dma := { s1.dma with ch := s1.dma.ch.set! ch d2 } }
  if irqEn then
    { s2 with irq := { s2.irq with if_ := s2.irq.if_ ||| dmaIrqBit ch } }
  else s2

/-- Fire one channel on CNT_H enable rising edge (immediate timing only). -/
def fireDmaCh (s : AGBState) (old : AgbDma) (ch : Nat) : AGBState :=
  let od := old.ch.getD ch {}
  let nd := s.dma.ch.getD ch {}
  let oldEn := ((od.cnt_h >>> 15) &&& 1) == 1
  let newEn := ((nd.cnt_h >>> 15) &&& 1) == 1
  let timing := (nd.cnt_h.toNat >>> 12) &&& 0x3
  if !oldEn && newEn && timing == 0 then doDma s ch else s

/-- Run one VBlank-timed channel if enabled (called on vc == 160 entry). -/
def runVBlankCh (s : AGBState) (ch : Nat) : AGBState :=
  let d := s.dma.ch.getD ch {}
  let en := ((d.cnt_h >>> 15) &&& 1) == 1
  let timing := (d.cnt_h.toNat >>> 12) &&& 0x3
  if en && timing == 1 then doDma s ch else s

/-- Run all VBlank-timed DMAs (HBlank timing stays pending: no hpos yet). -/
def runVBlankDma (s : AGBState) : AGBState :=
  runVBlankCh (runVBlankCh (runVBlankCh (runVBlankCh s 0) 1) 2) 3

/-- Push a 32-bit word into a FIFO, LSB first (GBATEK: Data 0 in the
    least significant byte is replayed first). -/
def apuFifoWrite32 (s : AGBState) (w : Nat) (v : UInt32) : AGBState :=
  let s := apuFifoPush s w v.toUInt8
  let s := apuFifoPush s w (v >>> 8).toUInt8
  let s := apuFifoPush s w (v >>> 16).toUInt8
  apuFifoPush s w (v >>> 24).toUInt8

/-- Sound-DMA burst: 4 words from the channel source into the FIFO
    (GBATEK refill procedure); source steps per the channel config. -/
def soundDmaWords : AGBState → UInt32 → Nat → Nat → Int → AGBState × UInt32
  | s, sad, _, 0, _ => (s, sad)
  | s, sad, w, k + 1, sstep =>
    let v := memRead32 s sad
    soundDmaWords (apuFifoWrite32 s w v) (addW32 sad sstep) w k sstep

/-- Channel `ch` armed for FIFO `w` (enabled, special timing, dest = the
    FIFO port; only channels 1-2 feed sound per GBATEK). -/
def dmaSoundArmed (s : AGBState) (ch w : Nat) : Bool :=
  let d := s.dma.ch.getD ch {}
  let want := if w == 0 then 0x040000A0 else 0x040000A4
  ((d.cnt_h >>> 15) &&& 1) == 1 && (d.cnt_h.toNat >>> 12) &&& 0x3 == 3
    && d.dad.toNat == want

/-- Refill FIFO `w` from its armed sound-DMA channel (repeat keeps the
    channel live, like `doDma`; IRQ on completion when enabled). -/
def apuSoundDma (s : AGBState) (w : Nat) : AGBState :=
  let ch := if dmaSoundArmed s 1 w then 1
            else if dmaSoundArmed s 2 w then 2 else 99
  if ch == 99 then s
  else
    let d := s.dma.ch.getD ch {}
    let srcC := (d.cnt_h.toNat >>> 7) &&& 0x3
    let sstep : Int :=
      if srcC == 1 then -4 else if srcC == 2 then 0 else 4
    let (s, sad) := soundDmaWords s d.sad w 4 sstep
    let rep := ((d.cnt_h >>> 9) &&& 1) == 1
    let irqEn := ((d.cnt_h >>> 14) &&& 1) == 1
    let newH := if rep then d.cnt_h else d.cnt_h &&& (0x7FFF : UInt16)
    let s :=
      { s with dma := { s.dma with ch := s.dma.ch.set! ch { d with sad := sad, cnt_h := newH } } }
    if irqEn then
      { s with irq := { s.irq with if_ := s.irq.if_ ||| dmaIrqBit ch } }
    else s

/-- One FIFO's share of timer `i`'s overflow: pop a byte, then refill
    via DMA when ≤ 16 bytes remain (GBATEK playback procedure). -/
def apuFifoTick (s : AGBState) (w i : Nat) : AGBState :=
  let sel := ((s.apu.cntH.toNat >>> (10 + w * 4)) &&& 1)
  if sel != i then s
  else
    let f := fifoPop (if w == 0 then s.apu.fifoA else s.apu.fifoB)
    let s :=
      if w == 0 then { s with apu := { s.apu with fifoA := f } }
      else { s with apu := { s.apu with fifoB := f } }
    if fifoSize f <= 16 then apuSoundDma s w else s

/-- Timer-overflow share for sound (only timers 0/1 selectable). -/
def apuTimerOverflow : AGBState → Nat → Nat → AGBState
  | s, _, 0 => s
  | s, i, o + 1 =>
    apuTimerOverflow (apuFifoTick (apuFifoTick s 0 i) 1 i) i o


/-- IO-range byte write (FIFO push / banked wave / generic lane sync).
    Split out so no dispatch chain exceeds the old `split` budget. -/
def memWrite8IO (s : AGBState) (a : Nat) (v : UInt8) : AGBState :=
  if 0x040000A0 <= a && a < 0x040000A8 then
    -- sound FIFO: each byte pushed (sample order = write order)
    apuFifoPush s ((a - 0x040000A0) / 4) v
  else if 0x04000090 <= a && a < 0x040000A0 then
    -- wave RAM: CPU sees the non-playing bank
    { s with apu := apuWaveWrite s.apu (a - 0x04000090) v }
  else
    let io := bset s.io (a - 0x04000000) v
    let s := { s with io := io }
    if a == 0x04000208 then { s with irq := { s.irq with ime := (v.toNat &&& 1) == 1 } }
    else
      let lane := a - (a % 2)
      syncIo16 s lane (bget16LE s.io (lane - 0x04000000))

/-- Write a byte by raw address (worker: no `let`, so `split` sees
    the dispatch chain directly; `memWrite8` coerces at the boundary). -/
def memWrite8Nat (s : AGBState) (a : Nat) (v : UInt8) : AGBState :=
  if 0x02000000 <= a && a < 0x03000000 then
    { s with ewram := bset s.ewram (mirrorIdx 0x02000000 0x40000 a) v }
  else if 0x03000000 <= a && a < 0x04000000 then
    { s with iwram := bset s.iwram (mirrorIdx 0x03000000 0x8000 a) v }
  else if 0x04000000 <= a && a < 0x05000000 then memWrite8IO s a v
  else if 0x05000000 <= a && a < 0x06000000 then
    { s with pal := bset s.pal (mirrorIdx 0x05000000 0x400 a) v }
  else if 0x06000000 <= a && a < 0x07000000 then
    { s with vram := bset s.vram (vramIdx a) v }
  else if 0x07000000 <= a && a < 0x08000000 then
    { s with oam := bset s.oam (mirrorIdx 0x07000000 0x400 a) v }
  else if 0x0E000000 <= a && a < 0x10000000 then
    saveWrite8 s ((a - 0x0E000000) % 0x10000) v
  else if (s.save.kind == .eeprom4k || s.save.kind == .eeprom64k)
      && 0x0D000000 <= a && a < 0x0E000000 then
    -- EEPROM serial window: one bit (D0) per bus access.
    { s with save := { s.save with
      eeprom := eepromWriteBit s.save.eeprom ((v.toNat &&& 1) == 1) } }
  else s

/-- Write a byte; IO bytes merge into their 16-bit lane for struct sync
    (so DMA-enable high bytes fire); IE/IF lanes stay shadow-only on
    byte writes, IME byte 0x04000208 still takes effect. -/
def memWrite8 (s : AGBState) (addr : UInt32) (v : UInt8) : AGBState :=
  memWrite8Nat s addr.toNat v

/-- 16-bit sound-port write (FIFO halves / wave word). The `else`
    arm is unreachable from `memWrite16IO` (guarded by the caller);
    it returns `s` unchanged. -/
def memWrite16Snd (s : AGBState) (a : Nat) (v : UInt16) : AGBState :=
  if a == 0x040000A0 || a == 0x040000A2
      || a == 0x040000A4 || a == 0x040000A6 then
    -- sound FIFO word halves: two byte pushes, LSB first
    let w := (a - 0x040000A0) / 4
    apuFifoPush (apuFifoPush s w v.toUInt8) w (v >>> 8).toUInt8
  else if 0x04000090 <= a && a < 0x040000A0 && a % 2 == 0 then
    -- wave RAM word: banked bytes (CPU-visible bank)
    let s := { s with apu := apuWaveWrite s.apu (a - 0x04000090) v.toUInt8 }
    { s with apu := apuWaveWrite s.apu (a - 0x04000090 + 1) (v >>> 8).toUInt8 }
  else s

/-- Lanes with struct sync on 16-bit writes (opaque predicate so
    `split` never traverses the 34-way condition). -/
def isSyncLane16 (a : Nat) : Bool :=
  a == 0x04000000 || a == 0x04000004 || a == 0x04000100
    || a == 0x04000102 || a == 0x04000104 || a == 0x04000106
    || a == 0x04000108 || a == 0x0400010A || a == 0x0400010C
    || a == 0x0400010E || a == 0x04000132
    || a == 0x04000050 || a == 0x04000052 || a == 0x04000054
    || a == 0x04000060 || a == 0x04000062 || a == 0x04000064
    || a == 0x04000068 || a == 0x0400006C || a == 0x04000070
    || a == 0x04000072 || a == 0x04000074 || a == 0x04000078
    || a == 0x0400007C || a == 0x04000080 || a == 0x04000082
    || a == 0x04000084 || a == 0x04000088
    || (0x04000008 <= a && a <= 0x0400001E)
    || (0x040000B0 <= a && a <= 0x040000DE)

/-- 16-bit IO write by raw address (worker: no `let`, so `split` sees
    the dispatch chain directly). -/
def memWrite16IO (s : AGBState) (a : Nat) (v : UInt16) : AGBState :=
  if a == 0x04000200 then
    let irq := { s.irq with ie := v }
    { s with irq := irq, io := bset16LE s.io 0x200 v }
  else if a == 0x04000202 then
    -- IF write-1-to-clear
    let lowered := s.irq.if_ &&& ~~~v
    let irq := { s.irq with if_ := lowered }
    { s with irq := irq, io := bset16LE s.io 0x202 lowered }
  else if a == 0x04000208 then
    let irq := { s.irq with ime := (v &&& 1) != 0 }
    { s with irq := irq, io := bset16LE s.io 0x208 v }
  -- DMA CNT_H lanes fire immediate transfers on the enable rising
  -- edge (checked per channel against the pre-write DMA state).
  else if a == 0x040000BA then
    let s1 := syncIo16 { s with io := bset16LE s.io (a - 0x04000000) v } a v
    fireDmaCh s1 s.dma 0
  else if a == 0x040000C6 then
    let s1 := syncIo16 { s with io := bset16LE s.io (a - 0x04000000) v } a v
    fireDmaCh s1 s.dma 1
  else if a == 0x040000D2 then
    let s1 := syncIo16 { s with io := bset16LE s.io (a - 0x04000000) v } a v
    fireDmaCh s1 s.dma 2
  else if a == 0x040000DE then
    let s1 := syncIo16 { s with io := bset16LE s.io (a - 0x04000000) v } a v
    fireDmaCh s1 s.dma 3
  else if (a == 0x040000A0 || a == 0x040000A2
      || a == 0x040000A4 || a == 0x040000A6)
      || (0x04000090 <= a && a < 0x040000A0 && a % 2 == 0) then
    memWrite16Snd s a v
  else if isSyncLane16 a then
    syncIo16 { s with io := bset16LE s.io (a - 0x04000000) v } a v
  else { s with io := bset16LE s.io (a - 0x04000000) v }

def memWrite16 (s : AGBState) (addr : UInt32) (v : UInt16) : AGBState :=
  if 0x04000000 <= addr.toNat && addr.toNat < 0x04000400 then
    memWrite16IO s addr.toNat v
  else
    memWrite8 (memWrite8 s addr v.toUInt8) (addr + 1) (v >>> 8).toUInt8

def memWrite32 (s : AGBState) (addr : UInt32) (v : UInt32) : AGBState :=
  memWrite16 (memWrite16 s addr v.toUInt16) (addr + 2) (v >>> 16).toUInt16

-- ── Waitstates (GBATEK access-time table; WAITCNT-driven GamePak) ──
-- Access = 1 + waitstates. Prefetch buffer (WAITCNT.14), 128K-block
-- N-forcing, 0x4000800 WRAM control and video-contention +1 are
-- deferred non-goals (documented); bursts charge N-each.

/-- WAITCNT shadow (0x04000204); reset default 0 = N:4 S:2 SRAM:4. -/
def waitcnt (s : AGBState) : Nat := (bget16LE s.io 0x204).toNat

/-- Sequential-fragment cost for WS region 0/1/2. -/
def sWaitFor (ws wc : Nat) : Nat :=
  if ws == 0 then 1 + sWait0 ((wc >>> 4) &&& 1)
  else if ws == 1 then 1 + sWait1 ((wc >>> 7) &&& 1)
  else 1 + sWait2 ((wc >>> 10) &&& 1)

/-- Which WS region (0/1/2) for a GamePak ROM address. -/
def wsOf (a : Nat) : Nat :=
  if a < 0x0A000000 then 0 else if a < 0x0C000000 then 1 else 2

/-- N-fragment cost of one access of `width` bytes at `addr`. -/
def memCostN (s : AGBState) (addr : UInt32) (width : Nat) : Nat :=
  let a := addr.toNat
  let wc := waitcnt s
  if a < 0x4000 then 1
  else if 0x02000000 <= a && a < 0x03000000 then (if width == 32 then 6 else 3)
  else if 0x03000000 <= a && a < 0x04000000 then 1
  else if 0x04000000 <= a && a < 0x05000000 then 1
  else if 0x05000000 <= a && a < 0x06000000 then (if width == 32 then 2 else 1)
  else if 0x06000000 <= a && a < 0x07000000 then (if width == 32 then 2 else 1)
  else if 0x07000000 <= a && a < 0x08000000 then 1
  else if 0x08000000 <= a && a < 0x0A000000 then 1 + nWait ((wc >>> 2) &&& 3)
  else if 0x0A000000 <= a && a < 0x0C000000 then 1 + nWait ((wc >>> 5) &&& 3)
  else if 0x0C000000 <= a && a < 0x0E000000 then 1 + nWait ((wc >>> 8) &&& 3)
  else if 0x0E000000 <= a && a < 0x10000000 then 1 + nWait (wc &&& 3)
  else 1

/-- Full access cost: 32-bit GamePak ROM splits N + S (16-bit bus);
    8-bit-bus SRAM scales by byte count; else single N fragment. -/
def memCost (s : AGBState) (addr : UInt32) (width : Nat) : Nat :=
  let a := addr.toNat
  if 0x08000000 <= a && a < 0x0E000000 then
    if width == 32 then memCostN s addr 16 + sWaitFor (wsOf a) (waitcnt s)
    else memCostN s addr width
  else if 0x0E000000 <= a && a < 0x10000000 then
    (width / 8) * (1 + nWait (waitcnt s &&& 3))
  else memCostN s addr width

/-- Memory waitstates for one Thumb instruction (pre-state addresses).
    Pure ALU/branch/SWI cost 0 here; their CPU base costs are unchanged.
    Destination registers never affect cost (address-only). -/
def execMemCostT (s : AGBState) (ins : ThumbInstr) : Nat :=
  match ins with
  | .strImm _ rn off => memCost s (s.regs.get rn + w32 off) 32
  | .ldrImm _ rn off => memCost s (s.regs.get rn + w32 off) 32
  | .strbImm _ rn off => memCost s (s.regs.get rn + w32 off) 8
  | .ldrbImm _ rn off => memCost s (s.regs.get rn + w32 off) 8
  | .strhImm _ rn off => memCost s (s.regs.get rn + w32 off) 16
  | .ldrhImm _ rn off => memCost s (s.regs.get rn + w32 off) 16
  | .strReg _ rn rm => memCost s (s.regs.get rn + s.regs.get rm) 32
  | .ldrReg _ rn rm => memCost s (s.regs.get rn + s.regs.get rm) 32
  | .strbReg _ rn rm => memCost s (s.regs.get rn + s.regs.get rm) 8
  | .ldrbReg _ rn rm => memCost s (s.regs.get rn + s.regs.get rm) 8
  | .strhReg _ rn rm => memCost s (s.regs.get rn + s.regs.get rm) 16
  | .ldrhReg _ rn rm => memCost s (s.regs.get rn + s.regs.get rm) 16
  | .ldsbReg _ rn rm => memCost s (s.regs.get rn + s.regs.get rm) 16
  | .ldshReg _ rn rm => memCost s (s.regs.get rn + s.regs.get rm) 16
  | .strSp _ off => memCost s (s.regs.get 13 + w32 off) 32
  | .ldrSp _ off => memCost s (s.regs.get 13 + w32 off) 32
  | .ldrLit _ off =>
    let base := ((s.regs.pc.toNat + 4) / 4) * 4
    memCost s (w32 (base + off)) 32
  | .push lr mask =>
    let n := popcount mask + (if lr then 1 else 0)
    n * memCost s (s.regs.get 13 - w32 (4 * n)) 32
  | .pop pcBit mask =>
    let n := popcount mask + (if pcBit then 1 else 0)
    n * memCost s (s.regs.get 13) 32
  | .stm rb mask =>
    let xs := regList mask
    if xs == [] then memCost s (s.regs.get rb) 32
    else popcount mask * memCost s (s.regs.get rb) 32
  | .ldm rb mask =>
    let xs := regList mask
    if xs == [] then memCost s (s.regs.get rb) 32
    else popcount mask * memCost s (s.regs.get rb) 32
  | _ => 0

/-- Memory waitstates for one ARM instruction. -/
def execMemCostA (s : AGBState) (ins : ArmInstr) : Nat :=
  match ins with
  | .memImm _ _ _ b _ _ rn _ off12 =>
    memCost s (s.regs.get rn + w32 off12) (if b then 8 else 32)
  | .memReg _ _ _ b _ _ rn _ rm _ _ =>
    memCost s (s.regs.get rn + s.regs.get rm) (if b then 8 else 32)
  | .memH _ _ _ _ _ _ _ rn _ _ _ =>
    memCost s (s.regs.get rn) 16
  | .ldmStm _ _ _ _ _ _ rn mask =>
    let xs := regList16 mask
    if xs == [] then memCost s (s.regs.get rn) 32
    else popcount16 mask * memCost s (s.regs.get rn) 32
  | .swp _ b rn _ _ =>
    memCost s (s.regs.get rn) (if b then 8 else 32) * 2
  | _ => 0

-- ── ALU flag helpers (32-bit) ──

structure NZCV where
  n : Bool
  z : Bool
  c : Bool
  v : Bool
deriving DecidableEq, Repr

def add32Flags (x y : UInt32) : UInt32 × NZCV :=
  let r := x + y
  let n := bitGet32 r 31
  let z := r == 0
  let c := r.toNat < x.toNat  -- wrapped iff result < operand (no carry-in)
  let sx := bitGet32 x 31; let sy := bitGet32 y 31; let sr := bitGet32 r 31
  let v := (sx == sy) && (sr != sx)
  (r, { n, z, c, v })

def sub32Flags (x y : UInt32) : UInt32 × NZCV :=
  let r := x - y
  let n := bitGet32 r 31
  let z := r == 0
  let c := x.toNat >= y.toNat  -- NOT borrow
  let sx := bitGet32 x 31; let sy := bitGet32 y 31; let sr := bitGet32 r 31
  let v := (sx != sy) && (sr != sx)
  (r, { n, z, c, v })

/-- ADC: x + y + carry. V uses the operand signs (carry cannot change it). -/
def adcFlags (x y : UInt32) (c : Bool) : UInt32 × NZCV :=
  let k : Nat := if c then 1 else 0
  let r := x + y + w32 k
  let n := bitGet32 r 31
  let z := r == 0
  let cc := x.toNat + y.toNat + k >= 0x100000000
  let sx := bitGet32 x 31; let sy := bitGet32 y 31; let sr := bitGet32 r 31
  let v := (sx == sy) && (sr != sx)
  (r, { n, z, c := cc, v })

/-- SBC: x - y - NOT-carry. C = NOT borrow; V uses y's sign (standard). -/
def sbcFlags (x y : UInt32) (c : Bool) : UInt32 × NZCV :=
  let b : Nat := if c then 0 else 1
  let r := x - y - w32 b
  let n := bitGet32 r 31
  let z := r == 0
  let cc := x.toNat >= y.toNat + b
  let sx := bitGet32 x 31; let sy := bitGet32 y 31; let sr := bitGet32 r 31
  let v := (sx != sy) && (sr != sx)
  (r, { n, z, c := cc, v })

/-- ALU two-operand result: (value, flags). No-write ops (TST/CMP/CMN)
    return the old Rd so the executor always writes back uniformly.
    ARM ARM DDI 0100I, Thumb data-processing: logical ops leave C
    (from no shifter) and V untouched; MUL destroys C/V (model: kept). -/
def aluRes (op : Nat) (x y : UInt32) (c0 : Bool) : UInt32 × NZCV :=
  match op with
  | 0 => let r := x &&& y; (r, { n := bitGet32 r 31, z := r == 0, c := c0, v := false })
  | 1 => let r := x ^^^ y; (r, { n := bitGet32 r 31, z := r == 0, c := c0, v := false })
  | 2 => let (r, c) := lslRC x (y.toNat % 256) c0; (r, { n := bitGet32 r 31, z := r == 0, c := c, v := false })
  | 3 => let (r, c) := lsrRC x (y.toNat % 256) c0; (r, { n := bitGet32 r 31, z := r == 0, c := c, v := false })
  | 4 => let (r, c) := asrRC x (y.toNat % 256) c0; (r, { n := bitGet32 r 31, z := r == 0, c := c, v := false })
  | 5 => adcFlags x y c0
  | 6 => let (r, c) := rorRC x (y.toNat % 256) c0; (r, { n := bitGet32 r 31, z := r == 0, c := c, v := false })
  | 7 => sbcFlags x y c0
  | 8 => let r := x &&& y; (x, { n := bitGet32 r 31, z := r == 0, c := c0, v := false })
  | 9 => sub32Flags 0 y
  | 10 => let (_, f) := sub32Flags x y; (x, f)
  | 11 => let (_, f) := add32Flags x y; (x, f)
  | 12 => let r := x ||| y; (r, { n := bitGet32 r 31, z := r == 0, c := c0, v := false })
  | 13 => let r := x * y; (r, { n := bitGet32 r 31, z := r == 0, c := c0, v := false })
  | 14 => let r := x &&& ~~~y; (r, { n := bitGet32 r 31, z := r == 0, c := c0, v := false })
  | _ => let r := ~~~y; (r, { n := bitGet32 r 31, z := r == 0, c := c0, v := false })

def applyNZCV (s : AGBState) (f : NZCV) : AGBState :=
  { s with regs := { s.regs with cpsr := cpsrSetNZCV s.regs.cpsr f.n f.z f.c f.v } }

/-- Pure-register NZCV apply (fast path threads `regs` without an
    intermediate state commit; identical result by construction). -/
def applyNZCVRegs (regs : ArmRegs) (f : NZCV) : ArmRegs :=
  { regs with cpsr := cpsrSetNZCV regs.cpsr f.n f.z f.c f.v }

/-- The register half of `applyNZCV` agrees with the pure version. -/
theorem applyNZCV_regs_eq (s : AGBState) (regs1 : ArmRegs) (f : NZCV) :
    (applyNZCV { s with regs := regs1 } f).regs
      = applyNZCVRegs regs1 f := by
  rfl

-- ── HLE SWI + real exception entry ──

/-- Halt wake condition: any enabled IRQ in the wait mask
    (`waitMask == 0` = plain HALT: any enabled IRQ). -/
def haltWake (s : AGBState) : Bool :=
  let m : UInt16 := if s.waitMask == 0 then 0xFFFF else s.waitMask
  ((s.irq.ie &&& s.irq.if_) &&& m) != 0

-- ── BIOS HLE workers (Phase 2; GBATEK "BIOS Functions") ──

def toSigned32 (x : UInt32) : Int :=
  if bitGet32 x 31 then (x.toNat : Int) - 0x100000000 else x.toNat

def intToW32 (v : Int) : UInt32 :=
  w32 ((v.emod 0x100000000).toNat)

/-- Fill `len` bytes at `pos` with zero (fuel recursion; bounds-safe). -/
def clearBytes : ByteArray → Nat → Nat → ByteArray
  | b, _, 0 => b
  | b, pos, k + 1 => clearBytes (bset b pos 0) (pos + 1) k

/-- RegisterRamReset region helpers (one bit each; nested calls keep
    every proof surface tiny — a flag chain this size defeats `split`). -/
def biosRREwram (s : AGBState) (flags : UInt32) : AGBState :=
  if flags.toNat &&& 0x01 == 0 then s
  else { s with ewram := clearBytes s.ewram 0 0x40000 }

def biosRRIwram (s : AGBState) (flags : UInt32) : AGBState :=
  if flags.toNat &&& 0x02 == 0 then s
  else { s with iwram := clearBytes s.iwram 0 (0x8000 - 0x200) }

def biosRRPal (s : AGBState) (flags : UInt32) : AGBState :=
  if flags.toNat &&& 0x04 == 0 then s
  else { s with pal := clearBytes s.pal 0 0x400 }

def biosRRVram (s : AGBState) (flags : UInt32) : AGBState :=
  if flags.toNat &&& 0x08 == 0 then s
  else { s with vram := clearBytes s.vram 0 0x18000 }

def biosRROam (s : AGBState) (flags : UInt32) : AGBState :=
  if flags.toNat &&& 0x10 == 0 then s
  else { s with oam := clearBytes s.oam 0 0x400 }

def biosRRSnd (s : AGBState) (flags : UInt32) : AGBState :=
  if flags.toNat &&& 0x40 == 0 then s
  else { s with apu := {}, io := clearBytes s.io 0x60 0x48 }

def biosRRTimers (s : AGBState) (flags : UInt32) : AGBState :=
  if flags.toNat &&& 0x80 == 0 then s
  else
    let io := clearBytes s.io 0x100 0x10
    let io := clearBytes io 0xB0 0x30
    let io := clearBytes io 0x02 0x5A
    let io := clearBytes io 0x132 0x02
    let io := bset16LE io 0 0x0080
    { s with timers := {}, dma := {}, key := { s.key with cnt := 0 },
             ppu := { s.ppu with dispcnt := 0x0080, dispstat := 0 }, io := io }

/-- RegisterRamReset (SWI 01h): clear/scrub selected regions.
    Bit5 (SIO) is a no-op: no model yet (the SIODATA32
    LSB-destroy bug is N/A). Bit6 resets sound (regs/channels/FIFOs).
    Bit7 zeroes timers/DMA/KEYCNT/DISPSTAT and
    scrubs their shadows; IE/IF/IME are preserved. DISPCNT is always
    forced to 0x0080 (forced blank), struct + shadow. -/
def biosRegReset (s : AGBState) (flags : UInt32) : AGBState :=
  let s := biosRRTimers (biosRRSnd (biosRROam (biosRRVram (biosRRPal
    (biosRRIwram (biosRREwram s flags) flags) flags) flags) flags) flags) flags
  -- forced blank regardless of flags
  { s with ppu := { s.ppu with dispcnt := 0x0080 },
           io := bset16LE s.io 0 0x0080 }

/-- SoftReset (SWI 00h): read return flag, clear IWRAM top 0x200, zero
    R0-R12 + banked LR/SPSR, install stacks, enter SYS/ARM, jump to
    ROM (flag 0) or RAM by BX R14. Caches/TCM are NDS-only: N/A. -/
def biosSoftReset (s : AGBState) : AGBState :=
  let flag := bget s.iwram 0x7FFA
  let s := { s with iwram := clearBytes s.iwram 0x7E00 0x200 }
  let target : UInt32 := if flag == 0 then 0x08000000 else 0x02000000
  let regs := s.regs
  let r0 := Array.replicate 16 (0 : UInt32)
  let regs := { regs with
    r := ((r0.set! 13 0x03007F00).set! 14 target).set! 15 target,
    cpsr := 0x1F, spsr_svc := 0, spsr_irq := 0,
    r13_svc := 0x03007FE0, r14_svc := 0,
    r13_irq := 0x03007FA0, r14_irq := 0 }
  { s with regs := regs, halted := false, waitMask := 0 }

/-- Signed division (SWI 06h; DivArm swaps operands at the call site).
    Division by zero yields zeros (HW hangs; documented deviation). -/
def biosDiv (s : AGBState) (num den : UInt32) : AGBState :=
  let n := toSigned32 num
  let d := toSigned32 den
  if d == 0 then
    { s with regs := ((s.regs.set 0 0).set 1 0).set 3 0 }
  else
    let qn := n.natAbs / d.natAbs
    let rn := n.natAbs % d.natAbs
    let q : Int := if (n < 0) == (d < 0) then (qn : Int) else -((qn : Int))
    let r : Int := if n < 0 then -((rn : Int)) else (rn : Int)
    { s with regs := ((s.regs.set 0 (intToW32 q)).set 1 (intToW32 r)).set 3 (w32 qn) }

-- ── BIOS Phase 3: signed IO, sin table, arctan, affine, decompression ──
-- Reference: GBATEK "BIOS Functions" + mGBA bios.c (affine/arctan exact).

/-- Signed 16-bit bus read. -/
def readS16 (s : AGBState) (addr : UInt32) : Int :=
  signExt (memRead16 s addr).toNat 16

/-- Signed 32-bit bus read. -/
def readS32 (s : AGBState) (addr : UInt32) : Int :=
  toSigned32 (memRead32 s addr)

/-- Signed 16-bit write (wraps mod 2^16; shadow-only IO like dmaWrite). -/
def writeS16 (s : AGBState) (addr : UInt32) (v : Int) : AGBState :=
  dmaWrite16 s addr (w16 ((v.emod 65536).toNat))

/-- Signed 32-bit write (wraps mod 2^32). -/
def writeS32 (s : AGBState) (addr : UInt32) (v : Int) : AGBState :=
  dmaWrite32 s addr (w32 ((v.emod 0x100000000).toNat))

/-- BIOS sin quarter-table: round(256·sin(2πi/256)), i = 0..64. -/
def sinTabQ : Array Int :=
  #[0, 6, 13, 19, 25, 31, 38, 44, 50, 56, 62, 68, 74, 80, 86, 92, 98,
    104, 109, 115, 121, 126, 132, 137, 142, 147, 152, 157, 162, 167, 172,
    177, 181, 185, 190, 194, 198, 202, 206, 209, 213, 216, 220, 223, 226,
    229, 231, 234, 237, 239, 241, 243, 245, 247, 248, 250, 251, 252, 253,
    254, 255, 255, 256, 256, 256]

/-- Full-circle sin in 8.8 (idx 0..255 = 0..360°; upper 8 BIOS bits). -/
def agbSin (idx : Nat) : Int :=
  let q := (idx >>> 6) &&& 0x3
  let r := idx &&& 0x3F
  if q == 0 then sinTabQ.getD r 0
  else if q == 1 then sinTabQ.getD (64 - r) 0
  else if q == 2 then -(sinTabQ.getD r 0)
  else -(sinTabQ.getD (64 - r) 0)

/-- Wrap to signed 32-bit (matches HW/C wrapping arithmetic). -/
def wrap32i (v : Int) : Int :=
  ((v + 0x80000000).emod 0x100000000) - 0x80000000

/-- Wrapping multiply / add (BIOS polynomial arithmetic). -/
def wmulW (a b : Int) : Int := wrap32i (a * b)
def waddW (a b : Int) : Int := wrap32i (a + b)

/-- C-style truncating division (Lean `/` on Int is Euclidean). -/
def tdiv (a b : Int) : Int :=
  if b == 0 then 0
  else
    let q := a.natAbs / b.natAbs
    if (a < 0) == (b < 0) then (q : Int) else -((q : Int))

/-- BIOS ArcTan polynomial core (mGBA `_ArcTan`): returns (ret, r1a, r3b).
    Shifts are floor (`ediv`), matching ARM arithmetic shifts. -/
def arctanCore (i : Int) : Int × Int × Int :=
  let a := -((wrap32i (i * i)).ediv 16384)
  let b := waddW ((wmulW 0xA9 a).ediv 16384) 0x390
  let b := waddW ((wmulW b a).ediv 16384) 0x91C
  let b := waddW ((wmulW b a).ediv 16384) 0xFB6
  let b := waddW ((wmulW b a).ediv 16384) 0x16AA
  let b := waddW ((wmulW b a).ediv 16384) 0x2081
  let b := waddW ((wmulW b a).ediv 16384) 0x3651
  let b := waddW ((wmulW b a).ediv 16384) 0xA2F9
  ((wrap32i (i * b)).ediv 65536, a, b)

/-- BIOS ArcTan2 octant logic (mGBA `_ArcTan2`): returns (ret16, innerA).
    Fast paths ( either input zero) report `touched = false` so the worker
    preserves r1 exactly like the BIOS fast paths. -/
def arctan2Core (x y : Int) : Int × Int × Bool :=
  if y == 0 then (if x >= 0 then (0, 0, false) else (0x8000, 0, false))
  else if x == 0 then (if y >= 0 then (0x4000, 0, false) else (0xC000, 0, false))
  else if y >= 0 then
    if x >= 0 then
      if x >= y then
        let (r, a, _) := arctanCore (tdiv (y * 16384) x); (r, a, true)
      else
        let (r, a, _) := arctanCore (tdiv (x * 16384) y); (0x4000 - r, a, true)
    else if -x >= y then
      let (r, a, _) := arctanCore (tdiv (y * 16384) x); (r + 0x8000, a, true)
    else
      let (r, a, _) := arctanCore (tdiv (x * 16384) y); (0x4000 - r, a, true)
  else
    if x <= 0 then
      if -x > -y then
        let (r, a, _) := arctanCore (tdiv (y * 16384) x); (r + 0x8000, a, true)
      else
        let (r, a, _) := arctanCore (tdiv (x * 16384) y); (0xC000 - r, a, true)
    else if x >= -y then
      let (r, a, _) := arctanCore (tdiv (y * 16384) x); (r + 0x10000, a, true)
    else
      let (r, a, _) := arctanCore (tdiv (x * 16384) y); (0xC000 - r, a, true)

/-- Tiny park workers (kept separate so the dispatch body stays small
    for the `split` tactic: large branch bodies blow its internal simp). -/
def hleSwiHalt (s : AGBState) : AGBState :=
  { s with halted := true, waitMask := 0 }

def hleSwiVBlankWait (s : AGBState) : AGBState :=
  -- BIOS forcefully sets IME (GBATEK); without it no post-wait IRQ fires.
  { s with halted := true, waitMask := 1, irq := { s.irq with ime := true } }

def hleSwiSqrt (s : AGBState) : AGBState :=
  { s with regs := s.regs.set 0 (w32 (Nat.sqrt (s.regs.get 0).toNat)) }

def hleSwiIntrWait (s : AGBState) : AGBState × Bool :=
  let m := (s.regs.get 1 &&& 0xFFFF).toUInt16
  let s := { s with irq := { s.irq with ime := true } }
  -- r0 == 0: return immediately if a masked flag is already set.
  if s.regs.get 0 == 0 && (((s.irq.ie &&& s.irq.if_) &&& m) != 0) then (s, false)
  else ({ s with halted := true, waitMask := m }, false)

def hleSwiArcTan (s : AGBState) : AGBState :=
  let (ret, a, b) := arctanCore (toSigned32 (s.regs.get 0))
  { s with regs := ((s.regs.set 0 (intToW32 ret)).set 1 (intToW32 a)).set 3 (intToW32 b) }

def hleSwiArcTan2 (s : AGBState) : AGBState :=
  let (ret, a, touched) :=
    arctan2Core (toSigned32 (s.regs.get 0)) (toSigned32 (s.regs.get 1))
  let regs := (s.regs.set 0 ((intToW32 ret) &&& (0xFFFF : UInt16).toUInt32)).set 3 0x170
  { s with regs := if touched then regs.set 1 (intToW32 a) else regs }

/-- BgAffineSet core (mGBA `_BgAffineSet`, integer 8.8 fixed point):
    A = cos·sx, B = −sin·sx, C = sin·sy, D = cos·sy (all 8.8),
    start = orig − (A·cx + B·cy) with NO shift (8.8 × int stays 8.8).
    Rounding is floor (`ediv`); mGBA/HW use their own fixed point here. -/
def bgAffineLoop : AGBState → UInt32 → UInt32 → Nat → AGBState
  | s, _, _, 0 => s
  | s, src, dst, n + 1 =>
    let ox := readS32 s src
    let oy := readS32 s (src + 4)
    let cx := readS16 s (src + 8)
    let cy := readS16 s (src + 10)
    let sx := readS16 s (src + 12)
    let sy := readS16 s (src + 14)
    let idx := ((memRead16 s (src + 16)).toNat >>> 8) &&& 0xFF
    let sn := agbSin idx
    let cs := agbSin ((idx + 64) % 256)
    let a := (cs * sx).ediv 256
    let b := -((sn * sx).ediv 256)
    let c := (sn * sy).ediv 256
    let d := (cs * sy).ediv 256
    let rx := ox - (a * cx + b * cy)
    let ry := oy - (c * cx + d * cy)
    let s := writeS16 (writeS16 (writeS16 (writeS16 s dst a) (dst + 2) b) (dst + 4) c) (dst + 6) d
    let s := writeS32 (writeS32 s (dst + 8) rx) (dst + 12) ry
    bgAffineLoop s (src + 20) (dst + 16) n

/-- ObjAffineSet core (mGBA `_ObjAffineSet`): same matrix, entries stored
    with `diff`-byte stride, destination advancing `diff·4` per entry. -/
def objAffineLoop : AGBState → UInt32 → UInt32 → Nat → Nat → AGBState
  | s, _, _, 0, _ => s
  | s, src, dst, n + 1, diff =>
    let sx := readS16 s src
    let sy := readS16 s (src + 2)
    let idx := ((memRead16 s (src + 4)).toNat >>> 8) &&& 0xFF
    let sn := agbSin idx
    let cs := agbSin ((idx + 64) % 256)
    let a := (cs * sx).ediv 256
    let b := -((sn * sx).ediv 256)
    let c := (sn * sy).ediv 256
    let d := (cs * sy).ediv 256
    let s := writeS16 s dst a
    let s := writeS16 s (dst + w32 diff) b
    let s := writeS16 s (dst + w32 (diff * 2)) c
    let s := writeS16 s (dst + w32 (diff * 3)) d
    objAffineLoop s (src + 8) (dst + w32 (diff * 4)) n diff

def hleSwiBgAffine (s : AGBState) : AGBState :=
  bgAffineLoop s (s.regs.get 0) (s.regs.get 1) (s.regs.get 2).toNat

def hleSwiObjAffine (s : AGBState) : AGBState :=
  objAffineLoop s (s.regs.get 0) (s.regs.get 1) (s.regs.get 2).toNat (s.regs.get 3).toNat

/-- LZ77 match copy: `len` bytes from `dst − disp` (overlap-safe). -/
def lzCopy : AGBState → UInt32 → Nat → Nat → AGBState × UInt32
  | s, dst, _, 0 => (s, dst)
  | s, dst, disp, len + 1 =>
    let v := memRead8 s (dst - w32 disp)
    lzCopy (dmaWrite8 s dst v) (dst + 1) disp len

/-- LZ77 main loop: flags MSB-first, literals verbatim, matches (len+3,
    backref disp+1). Fuel covers output + flag bytes (malformed-overrun
    past the declared size is a documented deviation). -/
def lzLoop : AGBState → UInt32 → UInt32 → Nat → Nat → Nat → Nat → AGBState × UInt32 × UInt32
  | s, src, dst, _, _, _, 0 => (s, src, dst)
  | s, src, dst, rem, fb, fc, fuel + 1 =>
    if rem == 0 then (s, src, dst)
    else if fc == 0 then
      lzLoop s (src + 1) dst rem (memRead8 s src).toNat 8 fuel
    else
      let isComp := ((fb >>> 7) &&& 1) == 1
      let fb := (fb * 2) % 256
      let fc := fc - 1
      if !isComp then
        lzLoop (dmaWrite8 s dst (memRead8 s src)) (src + 1) (dst + 1) (rem - 1) fb fc fuel
      else
        let b0 := (memRead8 s src).toNat
        let b1 := (memRead8 s (src + 1)).toNat
        let len := ((b0 >>> 4) &&& 0xF) + 3
        let disp := ((b0 &&& 0xF) * 256 + b1) + 1
        let n := min len rem
        let (s, dst) := lzCopy s dst disp n
        lzLoop s (src + 2) dst (rem - n) fb fc fuel

def hleSwiLz (s : AGBState) : AGBState :=
  let src := s.regs.get 0
  let dst := s.regs.get 1
  -- Wram and Vram variants are byte-identical on valid input (the Vram
  -- disp=000h quirk is a documented deviation).
  if (src.toNat &&& 0x0E000000) == 0 then s
  else
    let size := (((memRead32 s src).toNat >>> 8) &&& 0xFFFFFF)
    (lzLoop s (src + 4) dst size 0 0 (size + size / 8 + 2)).1

/-- RL fill / verbatim inner loops. -/
def rlFill : AGBState → UInt32 → UInt8 → Nat → AGBState × UInt32
  | s, dst, _, 0 => (s, dst)
  | s, dst, v, n + 1 => rlFill (dmaWrite8 s dst v) (dst + 1) v n

def rlCopyN : AGBState → UInt32 → UInt32 → Nat → AGBState × UInt32 × UInt32
  | s, src, dst, 0 => (s, src, dst)
  | s, src, dst, n + 1 =>
    rlCopyN (dmaWrite8 s dst (memRead8 s src)) (src + 1) (dst + 1) n

/-- RL main loop: flag.7 selects fill ((len&0x7F)+3 × one byte) vs
    verbatim (len+1 bytes). -/
def rlLoop : AGBState → UInt32 → UInt32 → Nat → Nat → AGBState × UInt32 × UInt32
  | s, src, dst, _, 0 => (s, src, dst)
  | s, src, dst, rem, fuel + 1 =>
    if rem == 0 then (s, src, dst)
    else
      let flag := (memRead8 s src).toNat
      if flag >= 0x80 then
        let n := min ((flag &&& 0x7F) + 3) rem
        let v := memRead8 s (src + 1)
        let (s, dst) := rlFill s dst v n
        rlLoop s (src + 2) dst (rem - n) fuel
      else
        let n := min (flag + 1) rem
        let (s, src, dst) := rlCopyN s (src + 1) dst n
        rlLoop s src dst (rem - n) fuel

/-- Narrow (byte) tail padding: (4 − size mod 4) mod 4 zero bytes. -/
def rlPadB : AGBState → UInt32 → Nat → AGBState × UInt32
  | s, dst, 0 => (s, dst)
  | s, dst, n + 1 => rlPadB (dmaWrite8 s dst 0) (dst + 1) n

/-- Wide (16-bit) tail padding: mGBA-faithful 16-bit zero stores. -/
def rlPadW : AGBState → UInt32 → Nat → AGBState × UInt32
  | s, dst, 0 => (s, dst)
  | s, dst, n + 1 => rlPadW (dmaWrite16 s dst 0) (dst + 2) n

def hleSwiRl (s : AGBState) (wide : Bool) : AGBState :=
  let src := s.regs.get 0
  let dst := s.regs.get 1
  if (src.toNat &&& 0x0E000000) == 0 then s
  else
    let size := (((memRead32 s src).toNat >>> 8) &&& 0xFFFFFF)
    let (s, _, dst) := rlLoop s (src + 4) dst size (size + 1)
    if !wide then
      (rlPadB s dst ((4 - size % 4) % 4)).1
    else
      -- mGBA parity: odd dst advances silently and padding shrinks
      -- (Nat floor matches the no-store outcome), then 16-bit zero pads.
      let pad := (4 - size % 4) % 4
      let dstOdd := (dst.toNat % 2) == 1
      let dst := if dstOdd then dst + 1 else dst
      let pad := if dstOdd then pad - 1 else pad
      let stores := if pad == 0 then 0 else (pad + 1) / 2
      (rlPadW s dst stores).1

/-- Huffman bitstream cursor. -/
structure HuffSt where
  src : UInt32
  word : UInt32
  left : Nat
  node : Nat
  base : Nat

/-- Pop one stream bit (MSB first), loading rotated 32-bit words
    (ARM unaligned-LDR rotation, matching HW where our `memRead32`
    alone would not). -/
def huffNextBit (s : AGBState) (st : HuffSt) : AGBState × HuffSt × Nat :=
  if st.left == 0 then
    let w := rotr32 (memRead32 s st.src) (8 * (st.src.toNat % 4))
    (s, { st with word := w <<< 1, src := st.src + 4, left := 31 },
      ((w >>> 31) &&& 1).toNat)
  else
    (s, { st with word := st.word <<< 1, left := st.left - 1 },
      ((st.word >>> 31) &&& 1).toNat)

/-- Walk the tree to the next data unit (`none` on malformed/deep input).
    Node layout per GBATEK: bits0-5 child offset, bit6 RTerm, bit7 LTerm. -/
def huffWalk (s : AGBState) (st : HuffSt) : Nat → AGBState × HuffSt × Nat × Bool
  | 0 => (s, st, 0, false)
  | fuel + 1 =>
    let (s, st, bit) := huffNextBit s st
    let nb := (memRead8 s (w32 st.node)).toNat
    let off := nb &&& 0x3F
    let next := ((st.node &&& 0xFFFFFFFE) + off * 2 + 2)
    if bit == 1 then
      if ((nb >>> 6) &&& 1) == 1 then (s, st, (memRead8 s (w32 (next + 1))).toNat, true)
      else huffWalk s { st with node := next + 1 } fuel
    else
      if ((nb >>> 7) &&& 1) == 1 then (s, st, (memRead8 s (w32 next)).toNat, true)
      else huffWalk s { st with node := next } fuel

/-- Huffman output loop: `bits`-wide units packed LE into bytes
    (1/2/4/8 all divide 8; other widths are refused up front). -/
def huffLoop (s : AGBState) (dst : UInt32) (rem : Nat) (cur fill : Nat)
    (bits : Nat) (st : HuffSt) (maxD : Nat) : Nat → AGBState × UInt32
  | 0 => (s, dst)
  | fuel + 1 =>
    if rem == 0 then (s, dst)
    else
      let (s, st, u, done) := huffWalk s st maxD
      if !done then (s, dst)
      else
        let u := u &&& ((1 <<< bits) - 1)
        let cur := cur ||| (u <<< fill)
        let fill := fill + bits
        if fill == 8 then
          huffLoop (dmaWrite8 s dst (w8 cur)) (dst + 1) (rem - 1) 0 0 bits st maxD fuel
        else huffLoop s dst rem cur fill bits st maxD fuel

def hleSwiHuff (s : AGBState) : AGBState :=
  let src0 := (s.regs.get 0) &&& 0xFFFFFFFC
  let dst := s.regs.get 1
  if (src0.toNat &&& 0x0E000000) == 0 then s
  else
    let header := (memRead32 s src0).toNat
    let bits0 := header &&& 0xF
    let bits := if bits0 == 0 then 8 else bits0
    let outsize := (header >>> 8) &&& 0xFFFFFF
    if bits == 1 || (32 % bits) != 0 then s
    else
      let tsize := (memRead8 s (src0 + 4)).toNat * 2 + 1
      let base := src0.toNat + 5
      let st : HuffSt :=
        { src := w32 (base + tsize), word := 0, left := 0, node := base, base := base }
      (huffLoop s dst outsize 0 0 bits st (tsize * 2 + 8) (outsize * 8 + 8)).1

/-- BitUnPack core: `srcW`-bit units + offset (with zero-flag rule),
    packed LE into 32-bit words; trailing partial words are dropped
    (encoders size output to a multiple of 4). -/
def bitLoop (s : AGBState) (src dst : UInt32) (inB : Nat)
    (bitsLeft srcLen : Nat) (out : Nat) (outBits : Nat)
    (srcW dstW : Nat) (off : Nat) (addZero : Bool) : Nat → AGBState × UInt32 × UInt32
  | 0 => (s, src, dst)
  | fuel + 1 =>
    if srcLen == 0 && bitsLeft == 0 then (s, src, dst)
    else
      let (s, src, inB, bitsLeft, srcLen) :=
        if bitsLeft == 0 then
          (s, src + 1, (memRead8 s src).toNat, 8, srcLen - 1)
        else (s, src, inB, bitsLeft, srcLen)
      let scaled := inB &&& ((1 <<< srcW) - 1)
      let inB := inB >>> srcW
      let scaled := if scaled != 0 || addZero then scaled + off else scaled
      let bitsLeft := bitsLeft - srcW
      let out := out ||| (scaled <<< outBits)
      let outBits := outBits + dstW
      if outBits == 32 then
        let w := out &&& 0xFFFFFFFF
        let s := dmaWrite8 (dmaWrite8 (dmaWrite8 (dmaWrite8 s dst (w8 w))
          (dst + 1) (w8 (w >>> 8))) (dst + 2) (w8 (w >>> 16))) (dst + 3) (w8 (w >>> 24))
        bitLoop s src (dst + 4) inB bitsLeft srcLen 0 0 srcW dstW off addZero fuel
      else bitLoop s src dst inB bitsLeft srcLen out outBits srcW dstW off addZero fuel

def hleSwiBitUnPack (s : AGBState) : AGBState :=
  let src := s.regs.get 0
  let dst := s.regs.get 1
  let info := s.regs.get 2
  if (src.toNat &&& 0x0E000000) == 0 then s
  else
    let srcLen := (memRead16 s info).toNat
    let srcW := (memRead8 s (info + 2)).toNat
    let dstW := (memRead8 s (info + 3)).toNat
    let bias := (memRead32 s (info + 4)).toNat
    if !(srcW == 1 || srcW == 2 || srcW == 4 || srcW == 8) then s
    else if !(dstW == 1 || dstW == 2 || dstW == 4 || dstW == 8 || dstW == 16 || dstW == 32) then s
    else
      let off := bias &&& 0x7FFFFFFF
      let addZero := ((bias >>> 31) &&& 1) == 1
      (bitLoop s src dst 0 0 srcLen 0 0 srcW dstW off addZero (srcLen * 8 / srcW + 9)).1

/-- Diff-filter core: running sum mod 2^8/2^16, LE byte output
    (identical bytes for all width variants, matching mGBA). -/
def diffLoop (s : AGBState) (src dst : UInt32) (rem : Nat) (acc : Nat)
    (wide : Bool) : Nat → AGBState × UInt32
  | 0 => (s, dst)
  | fuel + 1 =>
    if rem == 0 then (s, dst)
    else
      let u := if wide then (memRead16 s src).toNat else (memRead8 s src).toNat
      let m := if wide then 65536 else 256
      let acc := (acc + u) % m
      if wide then
        diffLoop (dmaWrite16 s dst (w16 acc)) (src + 2) (dst + 2) (rem - 2) acc true fuel
      else
        diffLoop (dmaWrite8 s dst (w8 acc)) (src + 1) (dst + 1) (rem - 1) acc false fuel

def hleSwiDiff (s : AGBState) (inW : Nat) : AGBState :=
  let src0 := (s.regs.get 0) &&& 0xFFFFFFFC
  let dst := s.regs.get 1
  if (src0.toNat &&& 0x0E000000) == 0 then s
  else
    let outsize := (((memRead32 s src0).toNat >>> 8) &&& 0xFFFFFF)
    (diffLoop s (src0 + 4) dst outsize 0 (inW == 2) (outsize + 2)).1

/-- CpuSet worker (SWI 0Bh): r2 bits0-20 count (words/halves),
    bit24 fixed-source fill, bit26 32-bit unit. BIOS-area sources are
    silently refused (GBA/NDS7/DSi7). -/
def hleSwiCpuSet (s : AGBState) : AGBState :=
  let src := s.regs.get 0
  let dst := s.regs.get 1
  let r2 := (s.regs.get 2).toNat
  let is32 := ((r2 >>> 26) &&& 1) == 1
  let fixed := ((r2 >>> 24) &&& 1) == 1
  let count := r2 &&& 0x1FFFFF
  let unit : Int := if is32 then 4 else 2
  let un : Nat := if is32 then 4 else 2
  if src.toNat < 0x4000 then s
  else dmaRun s src dst count is32 (if fixed then 0 else unit) unit un

/-- CpuFastSet worker (SWI 0Ch): 32-bit words, GBA rounds count up to a
    multiple of 8, bit24 fill. -/
def hleSwiCpuFastSet (s : AGBState) : AGBState :=
  let src := s.regs.get 0
  let dst := s.regs.get 1
  let r2 := (s.regs.get 2).toNat
  let count := r2 &&& 0x1FFFFF
  let count8 := ((count + 7) / 8) * 8
  let fixed := ((r2 >>> 24) &&& 1) == 1
  if src.toNat < 0x4000 then s
  else dmaRun s src dst count8 true (if fixed then 0 else 4) 4 4

/-- HLE SWI dispatch, grouped so no single if-chain exceeds what the
    `split` tactic handles (one long chain blows its internal simp
    budget): system/halt (9), copy/math (6), decompression (7).
    Unknown numbers return `(state, true)` so the executor takes a real
    SVC exception (vector 0x08) instead of NOP-sliding.
    Copy timing is NOT charged (fixed 2-cycle SWI cost, documented);
    source alignment is unchecked (documented). -/
def hleSwiDecomp (s : AGBState) (imm : Nat) : AGBState × Bool :=
  if imm == SWI_BITUNPACK then (hleSwiBitUnPack s, false)
  else if imm == SWI_LZ77WRAM || imm == SWI_LZ77VRAM then (hleSwiLz s, false)
  else if imm == SWI_HUFF then (hleSwiHuff s, false)
  else if imm == SWI_RLWRAM then (hleSwiRl s false, false)
  else if imm == SWI_RLVRAM then (hleSwiRl s true, false)
  else if imm == SWI_DIFF8W || imm == SWI_DIFF8V then (hleSwiDiff s 1, false)
  else if imm == SWI_DIFF16 then (hleSwiDiff s 2, false)
  else (s, true)

def hleSwiCopy (s : AGBState) (imm : Nat) : AGBState × Bool :=
  if imm == SWI_CPUSET then (hleSwiCpuSet s, false)
  else if imm == SWI_CPUFASTSET then (hleSwiCpuFastSet s, false)
  else if imm == SWI_ARCTAN then (hleSwiArcTan s, false)
  else if imm == SWI_ARCTAN2 then (hleSwiArcTan2 s, false)
  else if imm == SWI_BGAFFINE then (hleSwiBgAffine s, false)
  else if imm == SWI_OBJAFFINE then (hleSwiObjAffine s, false)
  else hleSwiDecomp s imm

def hleSwi (s : AGBState) (imm : Nat) : AGBState × Bool :=
  if imm == SWI_SOFTRESET then (biosSoftReset s, false)
  else if imm == SWI_REGRAMRESET then (biosRegReset s (s.regs.get 0), false)
  else if imm == SWI_HALT then (hleSwiHalt s, false)
  else if imm == SWI_STOP then
    -- Stop: HW restricts wake to joypad/cart/SIO (all unmodeled), so this
    -- parks exactly like Halt until any enabled IRQ (documented).
    (hleSwiHalt s, false)
  else if imm == SWI_INTRWAIT then hleSwiIntrWait s
  else if imm == SWI_VBLANKWAIT then (hleSwiVBlankWait s, false)
  else if imm == SWI_DIV then (biosDiv s (s.regs.get 0) (s.regs.get 1), false)
  else if imm == SWI_DIVARM then (biosDiv s (s.regs.get 1) (s.regs.get 0), false)
  else if imm == SWI_SQRT then (hleSwiSqrt s, false)
  else hleSwiCopy s imm

/-- SVC entry (ARM ARM DDI 0100I, exception handling): SPSR_svc = old
    CPSR, LR_svc = SWI address + 4 (return lands past the SWI), PC = 0x08.
    I/F untouched (SWI masks neither). -/
def serviceSwi (s : AGBState) (swiPC : UInt32) : AGBState :=
  let old := s.regs
  let regs := { old with
    cpsr := excCpsr old.cpsr MODE_SVC false false,
    spsr_svc := old.cpsr,
    r14_svc := swiPC + 4,
    r := old.r.set! 15 0x08 }
  { s with regs := regs, halted := false }

/-- IRQ entry: SPSR_irq = old CPSR, LR_irq = resume PC + 4 (the
    embedded BIOS stub returns via `SUBS pc,lr,#4`, exactly like HW),
    PC = 0x18 (BIOS stub dispatches through [0x03007FFC]), IME off.
    No GBA HW priority exists (BIOS polls IF) — entry fires on any
    pending IRQ. -/
def serviceIrq (s : AGBState) : AGBState :=
  let old := s.regs
  let regs := { old with
    cpsr := excCpsr old.cpsr MODE_IRQ true false,
    spsr_irq := old.cpsr,
    r14_irq := old.pc + 4,
    r := old.r.set! 15 0x18 }
  let irq := { s.irq with ime := false }
  { s with regs := regs, irq := irq, halted := false }

/-- Exception return (MOVS PC,LR semantics): restore CPSR from the
    mode's SPSR and jump to its LR. Caller passes the banked pair. -/
def excReturn (s : AGBState) (spsr lr : UInt32) : AGBState :=
  { s with regs := { s.regs with cpsr := spsr, r := s.regs.r.set! 15 lr } }

-- ── Thumb executor: returns (state, cycles) ──

/-- Store ascending registers to ascending words (PUSH/STM core). -/
def pushRegs : AGBState → UInt32 → List Nat → AGBState
  | s, _, [] => s
  | s, addr, r :: rs =>
    pushRegs (memWrite32 s addr (s.regs.get r)) (addr + 4) rs

/-- Load ascending words into ascending registers (POP/LDM core). -/
def popRegs : AGBState → UInt32 → List Nat → AGBState
  | s, _, [] => s
  | s, addr, r :: rs =>
    popRegs ({ s with regs := s.regs.set r (memRead32 s addr) }) (addr + 4) rs

/-- Fix PC + T from a loaded PC value (POP {PC} / LDM {PC} / return). -/
def fixLoadedPC (s : AGBState) (v : UInt32) : AGBState :=
  let cpsr := if (v &&& 1) == 1 then bitSet32 s.regs.cpsr 5 else bitClear32 s.regs.cpsr 5
  { s with regs := { (s.regs.set 15 (v &&& 0xFFFFFFFE)) with cpsr := cpsr } }

-- ── ARM executor helpers ──

/-- ARM DataProc ALU: (value, flags). No-write ops (TST/TEQ/CMP/CMN)
    return old Rn so the executor writes back uniformly (same trick as
    `aluRes`). Logical ops take the shifter carry; MUL-class flag
    behavior (C/V kept) matches the model calibration. -/
def dpAlu (op : Nat) (x y : UInt32) (shC c0 : Bool) : UInt32 × NZCV :=
  match op with
  | 0 => let r := x &&& y; (r, { n := bitGet32 r 31, z := r == 0, c := shC, v := false })
  | 1 => let r := x ^^^ y; (r, { n := bitGet32 r 31, z := r == 0, c := shC, v := false })
  | 2 => sub32Flags x y
  | 3 => sub32Flags y x
  | 4 => add32Flags x y
  | 5 => adcFlags x y c0
  | 6 => sbcFlags x y c0
  | 7 => sbcFlags y x c0
  | 8 => let r := x &&& y; (x, { n := bitGet32 r 31, z := r == 0, c := shC, v := false })
  | 9 => let r := x ^^^ y; (x, { n := bitGet32 r 31, z := r == 0, c := shC, v := false })
  | 10 => let (_, f) := sub32Flags x y; (x, f)
  | 11 => let (_, f) := add32Flags x y; (x, f)
  | 12 => let r := x ||| y; (r, { n := bitGet32 r 31, z := r == 0, c := shC, v := false })
  | 13 => (y, { n := bitGet32 y 31, z := y == 0, c := shC, v := false })
  | 14 => let r := x &&& ~~~y; (r, { n := bitGet32 r 31, z := r == 0, c := shC, v := false })
  | _ => let r := ~~~y; (r, { n := bitGet32 r 31, z := r == 0, c := shC, v := false })

/-- MSR writable-bits mask from the field mask (f/s/x/c = bits 3..0).
    USR mode restricts to NZCV (0xF0000000); the s/x/c bytes hold no
    v4T state a user program may change. -/
def msrMask (mask : Nat) (priv : Bool) : UInt32 :=
  let f : UInt32 := if (mask >>> 3) &&& 1 == 1 then (if priv then 0xFF000000 else 0xF0000000) else 0
  let s : UInt32 := if (mask >>> 2) &&& 1 == 1 && priv then 0x00FF0000 else 0
  let x : UInt32 := if (mask >>> 1) &&& 1 == 1 && priv then 0x0000FF00 else 0
  let c : UInt32 := if (mask &&& 1) == 1 && priv then 0x000000FF else 0
  f ||| s ||| x ||| c

/-- Apply an MSR value under the field mask (CPSR or current SPSR). -/
def applyMsr (s : AGBState) (psr mask : Nat) (v : UInt32) : AGBState :=
  let priv := cpsrMode s.regs.cpsr != 0x10
  let m := msrMask mask priv
  if psr == 0 then
    { s with regs := { s.regs with cpsr := (s.regs.cpsr &&& ~~~m) ||| (v &&& m) } }
  else
    let cur := (spsrOf s.regs &&& ~~~m) ||| (v &&& m)
    { s with regs := setSpsr s.regs cur }

/-- ARM PC write: stays ARM (mask ~3); BX/fixLoadedPC handle T-switches. -/
def writePC (s : AGBState) (v : UInt32) : AGBState :=
  { s with regs := s.regs.set 15 (v &&& 0xFFFFFFFC) }

def execThumb (s : AGBState) (ins : ThumbInstr) : AGBState × Nat :=
  let pc := s.regs.pc
  match ins with
  | .movsImm rd imm =>
    let v := w32 imm
    let s := { s with regs := (s.regs.set rd v).set 15 (pc + 2) }
    (applyNZCV s { n := bitGet32 v 31, z := v == 0, c := cpsrC s.regs.cpsr, v := false }, 1)
  | .cmpImm rn imm =>
    let (_, f) := sub32Flags (s.regs.get rn) (w32 imm)
    let s := { s with regs := s.regs.set 15 (pc + 2) }
    (applyNZCV s f, 1)
  | .addImm rd imm =>
    let (r, f) := add32Flags (s.regs.get rd) (w32 imm)
    let s := { s with regs := (s.regs.set rd r).set 15 (pc + 2) }
    (applyNZCV s f, 1)
  | .subImm rd imm =>
    let (r, f) := sub32Flags (s.regs.get rd) (w32 imm)
    let s := { s with regs := (s.regs.set rd r).set 15 (pc + 2) }
    (applyNZCV s f, 1)
  | .addsImm rd rn imm =>
    let (r, f) := add32Flags (s.regs.get rn) (w32 imm)
    let s := { s with regs := (s.regs.set rd r).set 15 (pc + 2) }
    (applyNZCV s f, 1)
  | .subsImm rd rn imm =>
    let (r, f) := sub32Flags (s.regs.get rn) (w32 imm)
    let s := { s with regs := (s.regs.set rd r).set 15 (pc + 2) }
    (applyNZCV s f, 1)
  | .addsReg rd rn rm =>
    let (r, f) := add32Flags (s.regs.get rn) (s.regs.get rm)
    let s := { s with regs := (s.regs.set rd r).set 15 (pc + 2) }
    (applyNZCV s f, 1)
  | .subsReg rd rn rm =>
    let (r, f) := sub32Flags (s.regs.get rn) (s.regs.get rm)
    let s := { s with regs := (s.regs.set rd r).set 15 (pc + 2) }
    (applyNZCV s f, 1)
  | .lslImm rd rm sh =>
    let x := s.regs.get rm
    let r := if sh == 0 then x else x <<< sh.toUInt32
    let c := if sh == 0 then cpsrC s.regs.cpsr else bitGet32 x (32 - sh)
    let s := { s with regs := (s.regs.set rd r).set 15 (pc + 2) }
    (applyNZCV s { n := bitGet32 r 31, z := r == 0, c := c, v := false }, 1)
  | .lsrImm rd rm sh =>
    -- decoder already maps imm5 = 0 to 32
    let (r, c) := lsrRC (s.regs.get rm) sh (cpsrC s.regs.cpsr)
    let s := { s with regs := (s.regs.set rd r).set 15 (pc + 2) }
    (applyNZCV s { n := bitGet32 r 31, z := r == 0, c := c, v := false }, 1)
  | .asrImm rd rm sh =>
    let (r, c) := asrRC (s.regs.get rm) sh (cpsrC s.regs.cpsr)
    let s := { s with regs := (s.regs.set rd r).set 15 (pc + 2) }
    (applyNZCV s { n := bitGet32 r 31, z := r == 0, c := c, v := false }, 1)
  | .alu2 op rs rd =>
    let (r, f) := aluRes op (s.regs.get rd) (s.regs.get rs) (cpsrC s.regs.cpsr)
    let s := { s with regs := (s.regs.set rd r).set 15 (pc + 2) }
    (applyNZCV s f, 1)
  | .mul rs rd =>
    let r := s.regs.get rd * s.regs.get rs
    let s := { s with regs := (s.regs.set rd r).set 15 (pc + 2) }
    -- MUL destroys C/V on HW; model keeps them (documented calibration)
    (applyNZCV s { n := bitGet32 r 31, z := r == 0, c := cpsrC s.regs.cpsr, v := false }, 2)
  | .hiAdd rs rd =>
    let sv := if rs == 15 then pc + 4 else s.regs.get rs
    let dv := if rd == 15 then pc + 4 else s.regs.get rd
    let r := dv + sv
    let s := if rd == 15 then { s with regs := s.regs.set 15 (r &&& 0xFFFFFFFE) }
             else { s with regs := (s.regs.set rd r).set 15 (pc + 2) }
    (s, 1)
  | .hiCmp rs rd =>
    let sv := if rs == 15 then pc + 4 else s.regs.get rs
    let dv := if rd == 15 then pc + 4 else s.regs.get rd
    let (_, f) := sub32Flags dv sv
    let s := { s with regs := s.regs.set 15 (pc + 2) }
    (applyNZCV s f, 1)
  | .hiMov rs rd =>
    let sv := if rs == 15 then pc + 4 else s.regs.get rs
    let s := if rd == 15 then { s with regs := s.regs.set 15 (sv &&& 0xFFFFFFFE) }
             else { s with regs := (s.regs.set rd sv).set 15 (pc + 2) }
    (s, 1)
  | .strReg rd rn rm =>
    let s := memWrite32 s (s.regs.get rn + s.regs.get rm) (s.regs.get rd)
    ({ s with regs := s.regs.set 15 (pc + 2) }, 2)
  | .ldrReg rd rn rm =>
    let (s, v) := memRead32E s (s.regs.get rn + s.regs.get rm)
    ({ s with regs := (s.regs.set rd v).set 15 (pc + 2) }, 3)
  | .strbReg rd rn rm =>
    let s := memWrite8 s (s.regs.get rn + s.regs.get rm) (s.regs.get rd).toUInt8
    ({ s with regs := s.regs.set 15 (pc + 2) }, 2)
  | .ldrbReg rd rn rm =>
    let (s, t) := memRead8E s (s.regs.get rn + s.regs.get rm)
    ({ s with regs := (s.regs.set rd t.toUInt32).set 15 (pc + 2) }, 3)
  | .strhReg rd rn rm =>
    let s := memWrite16 s (s.regs.get rn + s.regs.get rm) (s.regs.get rd).toUInt16
    ({ s with regs := s.regs.set 15 (pc + 2) }, 2)
  | .ldrhReg rd rn rm =>
    let (s, t) := memRead16E s (s.regs.get rn + s.regs.get rm)
    ({ s with regs := (s.regs.set rd t.toUInt32).set 15 (pc + 2) }, 3)
  | .ldsbReg rd rn rm =>
    let (s, t) := memRead8E s (s.regs.get rn + s.regs.get rm)
    ({ s with regs := (s.regs.set rd (sx8 t)).set 15 (pc + 2) }, 3)
  | .ldshReg rd rn rm =>
    let (s, t) := memRead16E s (s.regs.get rn + s.regs.get rm)
    ({ s with regs := (s.regs.set rd (sx16 t)).set 15 (pc + 2) }, 3)
  | .strImm rd rn off =>
    let addr := s.regs.get rn + w32 off
    let s := memWrite32 s addr (s.regs.get rd)
    ({ s with regs := s.regs.set 15 (pc + 2) }, 2)
  | .ldrImm rd rn off =>
    let addr := s.regs.get rn + w32 off
    let (s, v) := memRead32E s addr
    ({ s with regs := (s.regs.set rd v).set 15 (pc + 2) }, 3)
  | .strbImm rd rn off =>
    let s := memWrite8 s (s.regs.get rn + w32 off) (s.regs.get rd).toUInt8
    ({ s with regs := s.regs.set 15 (pc + 2) }, 2)
  | .ldrbImm rd rn off =>
    let (s, t) := memRead8E s (s.regs.get rn + w32 off)
    ({ s with regs := (s.regs.set rd t.toUInt32).set 15 (pc + 2) }, 3)
  | .strhImm rd rn off =>
    let s := memWrite16 s (s.regs.get rn + w32 off) (s.regs.get rd).toUInt16
    ({ s with regs := s.regs.set 15 (pc + 2) }, 2)
  | .ldrhImm rd rn off =>
    let (s, t) := memRead16E s (s.regs.get rn + w32 off)
    ({ s with regs := (s.regs.set rd t.toUInt32).set 15 (pc + 2) }, 3)
  | .strSp rd off =>
    let s := memWrite32 s (s.regs.get 13 + w32 off) (s.regs.get rd)
    ({ s with regs := s.regs.set 15 (pc + 2) }, 2)
  | .ldrSp rd off =>
    let (s, v) := memRead32E s (s.regs.get 13 + w32 off)
    ({ s with regs := (s.regs.set rd v).set 15 (pc + 2) }, 3)
  | .ldrLit rd off =>
    -- pipeline: PC reads +4, word-aligned
    let base := ((pc.toNat + 4) / 4) * 4
    let (s, v) := memRead32E s (w32 (base + off))
    ({ s with regs := (s.regs.set rd v).set 15 (pc + 2) }, 3)
  | .adrPc rd off =>
    let base := ((pc.toNat + 4) / 4) * 4
    ({ s with regs := (s.regs.set rd (w32 (base + off))).set 15 (pc + 2) }, 1)
  | .adrSp rd off =>
    ({ s with regs := (s.regs.set rd (s.regs.get 13 + w32 off)).set 15 (pc + 2) }, 1)
  | .addSp off =>
    -- modular SP arithmetic (HW wraps; Int-toNat would clamp at 0)
    let sp := s.regs.get 13
    let r := if off < 0 then sp - w32 ((-off).toNat) else sp + w32 off.toNat
    ({ s with regs := (s.regs.set 13 r).set 15 (pc + 2) }, 1)
  | .push lr mask =>
    let xs := regList mask ++ (if lr then [14] else [])
    let n := popcount mask + (if lr then 1 else 0)
    let base := s.regs.get 13 - w32 (4 * n)
    let s1 := pushRegs s base xs
    ({ s1 with regs := (s1.regs.set 13 base).set 15 (pc + 2) }, n + 2)
  | .pop pcBit mask =>
    let xs := regList mask ++ (if pcBit then [15] else [])
    let n := popcount mask + (if pcBit then 1 else 0)
    let base := s.regs.get 13
    let s1 := popRegs s base xs
    let s2 := { s1 with regs := s1.regs.set 13 (base + w32 (4 * n)) }
    -- PC loaded from the stack wins over fallthrough (return path)
    if pcBit then (fixLoadedPC s2 (s2.regs.get 15), n + 3)
    else ({ s2 with regs := s2.regs.set 15 (pc + 2) }, n + 3)
  | .stm rb mask =>
    let xs := regList mask
    let base := s.regs.get rb
    if xs == [] then
      -- empty list: store PC, advance 0x40 (documented v4T-UNPREDICTABLE choice)
      let s1 := memWrite32 s base (s.regs.get 15)
      ({ s1 with regs := (s1.regs.set rb (base + 0x40)).set 15 (pc + 2) }, 4)
    else
      let n := popcount mask
      let s1 := pushRegs s base xs
      ({ s1 with regs := (s1.regs.set rb (base + w32 (4 * n))).set 15 (pc + 2) }, n + 2)
  | .ldm rb mask =>
    let xs := regList mask
    let base := s.regs.get rb
    if xs == [] then
      let v := memRead32 s base
      let s1 := fixLoadedPC s v
      ({ s1 with regs := s1.regs.set rb (base + 0x40) }, 4)
    else
      let n := popcount mask
      let s1 := popRegs s base xs
      -- writeback suppressed when Rb is in the list (loaded value wins)
      let s2 := if xs.contains rb then s1
                else { s1 with regs := s1.regs.set rb (base + w32 (4 * n)) }
      -- PC in the list wins over fallthrough (return-from-ARM path)
      if xs.contains 15 then (fixLoadedPC s2 (s2.regs.get 15), n + 3)
      else ({ s2 with regs := s2.regs.set 15 (pc + 2) }, n + 3)
  | .bcond cond off =>
    if condPass s.regs.cpsr cond then
      let tgt : Int := (pc.toNat : Int) + 4 + off
      ({ s with regs := s.regs.set 15 (intToW32 tgt) }, 3)
    else ({ s with regs := s.regs.set 15 (pc + 2) }, 1)
  | .b off =>
    -- pipeline: PC reads +4. `intToW32` (not `w32 tgt.toNat`: `Int.toNat`
    -- truncates negatives to 0, misrouting far-backward BL/B targets
    -- issued from low BIOS addresses — the BIOS-boot reboot loop).
    let tgt : Int := (pc.toNat : Int) + 4 + off
    ({ s with regs := s.regs.set 15 (intToW32 tgt) }, 3)
  | .blPre off =>
    let lr := intToW32 ((pc.toNat : Int) + 4 + off)
    ({ s with regs := (s.regs.set 14 lr).set 15 (pc + 2) }, 3)
  | .blSuf off =>
    let tgt : Int := (s.regs.get 14).toNat + off
    let ret := (pc + 2) ||| 1
    ({ s with regs := (s.regs.set 14 ret).set 15 (intToW32 tgt &&& 0xFFFFFFFE) }, 4)
  | .bx rm =>
    let a := s.regs.get rm
    let thumb := (a &&& 1) == 1
    let cpsr := if thumb then bitSet32 s.regs.cpsr 5 else bitClear32 s.regs.cpsr 5
    ({ s with regs := { (s.regs.set 15 (a &&& 0xFFFFFFFE)) with cpsr := cpsr } }, 3)
  | .swi imm =>
    let (sH, takeExc) := hleSwi s imm
    if takeExc then (serviceSwi sH pc, 2)
    else ({ sH with regs := sH.regs.set 15 (pc + 2) }, 2)
  | .nop => ({ s with regs := s.regs.set 15 (pc + 2) }, 1)

-- ── ARM executor: returns (state, cycles); fallthrough is pc + 4 ──

/-- Shared DataProc tail: ALU, S-flag handling, Rd=15 rules (S=1 →
    restore SPSR and follow its T; plain write stays ARM, masked).
    Costs are calibrated flat (pipeline refill folded in). -/
def execDp (s : AGBState) (op st rn rd : Nat) (y : UInt32) (shC : Bool) : AGBState × Nat :=
  let pc := s.regs.pc
  -- MOV/MVN ignore Rn; Rn=15 reads the ARM pipeline PC (+8)
  let x := if op == 13 || op == 15 then 0
           else if rn == 15 then pc + 8 else s.regs.get rn
  let (r, f) := dpAlu op x y shC (cpsrC s.regs.cpsr)
  -- TST/TEQ/CMP/CMN never write Rd (the Rd field is SBZ on HW)
  let wb := !(op == 8 || op == 9 || op == 10 || op == 11)
  if st == 1 then
    if rd == 15 then
      let nspsr := spsrOf s.regs
      let nt := bitGet32 nspsr 5
      ({ s with regs := { (s.regs.set 15
        (if nt then r &&& 0xFFFFFFFE else r &&& 0xFFFFFFFC)) with cpsr := nspsr } }, 1)
    else if wb then
      let s := { s with regs := (s.regs.set rd r).set 15 (pc + 4) }
      (applyNZCV s f, 1)
    else
      let s := { s with regs := s.regs.set 15 (pc + 4) }
      (applyNZCV s f, 1)
  else
    if !wb then ({ s with regs := s.regs.set 15 (pc + 4) }, 1)
    else if rd == 15 then (writePC s r, 1)
    else ({ s with regs := (s.regs.set rd r).set 15 (pc + 4) }, 1)

/-- Pre/post-index address + base writeback (post always writes back).
    Rn=15 reads PC+8 (ARM pipeline; the #1 commercial-boot killer). -/
def memAddrWB (s : AGBState) (rn : Nat) (p u w : Bool) (off : UInt32) :
    AGBState × UInt32 :=
  let base := if rn == 15 then s.regs.pc + 8 else s.regs.get rn
  if p then
    let eff := if u then base + off else base - off
    (if w then { s with regs := s.regs.set rn eff } else s, eff)
  else
    let wb := if u then base + off else base - off
    ({ s with regs := s.regs.set rn wb }, base)

def execArm (s : AGBState) (ins : ArmInstr) : AGBState × Nat :=
  let pc := s.regs.pc
  let cpsr := s.regs.cpsr
  let c0 := cpsrC cpsr
  match ins with
  | .dpImm c op st rn rd rot imm8 =>
    if !armCondPass cpsr c then ({ s with regs := s.regs.set 15 (pc + 4) }, 1)
    else
      let sh := rotr32 (w32 imm8) (rot * 2)
      let shC := if rot == 0 then c0 else bitGet32 sh 31
      execDp s op st rn rd sh shC
  | .dpReg c op st rn rd rm shTy shReg sa =>
    if !armCondPass cpsr c then ({ s with regs := s.regs.set 15 (pc + 4) }, 1)
    else
      let sv := s.regs.get rm
      let (shV, shC) :=
        if shTy == 3 && !shReg && sa == 0 then rrxRC sv c0
        else if shReg then armShiftReg shTy sv ((s.regs.get sa).toNat % 256) c0
        else armShiftReg shTy sv sa c0
      execDp s op st rn rd shV shC
  | .mul c acc st rd rn rm rs =>
    if !armCondPass cpsr c then ({ s with regs := s.regs.set 15 (pc + 4) }, 1)
    else
      let r := s.regs.get rm * s.regs.get rs + (if acc then s.regs.get rn else 0)
      let s := { s with regs := (s.regs.set rd r).set 15 (pc + 4) }
      (if st then applyNZCV s { n := bitGet32 r 31, z := r == 0, c := c0, v := false } else s, 2)
  | .mull c u acc st rdHi rdLo rm rs =>
    if !armCondPass cpsr c then ({ s with regs := s.regs.set 15 (pc + 4) }, 1)
    else
      let x := s.regs.get rm
      let y := s.regs.get rs
      let sx : Int := if bitGet32 x 31 then (x.toNat : Int) - 0x100000000 else x.toNat
      let sy : Int := if bitGet32 y 31 then (y.toNat : Int) - 0x100000000 else y.toNat
      let prod : Int :=
        (if u then (x.toNat : Int) * y.toNat else sx * sy)
        + (if acc then
            let hi := s.regs.get rdHi
            let lo := s.regs.get rdLo
            let a : Int := hi.toNat * 0x100000000 + lo.toNat
            if !u && bitGet32 hi 31 then a - 0x10000000000000000 else a
          else 0)
      let full : Nat :=
        ((((prod % 0x10000000000000000) + 0x10000000000000000) % 0x10000000000000000).toNat)
      let hi := w32 (full / 0x100000000)
      let lo := w32 (full % 0x100000000)
      let s := { s with regs := ((s.regs.set rdLo lo).set rdHi hi).set 15 (pc + 4) }
      (if st then
        applyNZCV s { n := bitGet32 hi 31, z := full == 0, c := c0, v := false }
       else s, 3)
  | .mrs c psr rd =>
    if !armCondPass cpsr c then ({ s with regs := s.regs.set 15 (pc + 4) }, 1)
    else
      let v := if psr == 0 then s.regs.cpsr else spsrOf s.regs
      ({ s with regs := (s.regs.set rd v).set 15 (pc + 4) }, 1)
  | .msrImm c psr mask rot imm8 =>
    if !armCondPass cpsr c then ({ s with regs := s.regs.set 15 (pc + 4) }, 1)
    else
      let s1 := applyMsr s psr mask (rotr32 (w32 imm8) (rot * 2))
      ({ s1 with regs := s1.regs.set 15 (pc + 4) }, 1)
  | .msrReg c psr mask rm =>
    if !armCondPass cpsr c then ({ s with regs := s.regs.set 15 (pc + 4) }, 1)
    else
      let s1 := applyMsr s psr mask (s.regs.get rm)
      ({ s1 with regs := s1.regs.set 15 (pc + 4) }, 1)
  | .memImm c p u b w l rn rd off12 =>
    if !armCondPass cpsr c then ({ s with regs := s.regs.set 15 (pc + 4) }, 1)
    else
      let (s1, a) := memAddrWB s rn p u w (w32 off12)
      if l then
        let (s1, v) := if b then
            let (s, t) := memRead8E s1 a; (s, t.toUInt32)
          else memRead32E s1 a
        -- Rd=15 is a branch (v4T: no state switch); never fall through it.
        (if rd == 15 then (writePC s1 v, 3)
         else ({ s1 with regs := (s1.regs.set rd v).set 15 (pc + 4) }, 3))
      else
        let s2 := if b then memWrite8 s1 a (s1.regs.get rd).toUInt8
                  else memWrite32 s1 a (s1.regs.get rd)
        ({ s2 with regs := s2.regs.set 15 (pc + 4) }, 2)
  | .memReg c p u b w l rn rd rm shTy amt5 =>
    if !armCondPass cpsr c then ({ s with regs := s.regs.set 15 (pc + 4) }, 1)
    else
      let sv := s.regs.get rm
      let offV :=
        if shTy == 3 && amt5 == 0 then (rrxRC sv c0).1
        else (armShiftReg shTy sv amt5 c0).1
      let (s1, a) := memAddrWB s rn p u w offV
      if l then
        let (s1, v) := if b then
            let (s, t) := memRead8E s1 a; (s, t.toUInt32)
          else memRead32E s1 a
        (if rd == 15 then (writePC s1 v, 3)
         else ({ s1 with regs := (s1.regs.set rd v).set 15 (pc + 4) }, 3))
      else
        let s2 := if b then memWrite8 s1 a (s1.regs.get rd).toUInt8
                  else memWrite32 s1 a (s1.regs.get rd)
        ({ s2 with regs := s2.regs.set 15 (pc + 4) }, 2)
  | .memH c p u w l h hh rn rd isImm off =>
    if !armCondPass cpsr c then ({ s with regs := s.regs.set 15 (pc + 4) }, 1)
    else
      let offV := if isImm then w32 off else s.regs.get off
      let (s1, a) := memAddrWB s rn p u w offV
      if l then
        let (s1, v) := if h then
            if hh then
              let (s, t) := memRead16E s1 a; (s, sx16 t)
            else
              let (s, t) := memRead16E s1 a; (s, t.toUInt32)
          else
            let (s, t) := memRead8E s1 a; (s, sx8 t)
        -- Rd=15 UNPREDICTABLE on v4T; model as a plain branch.
        (if rd == 15 then (writePC s1 v, 3)
         else ({ s1 with regs := (s1.regs.set rd v).set 15 (pc + 4) }, 3))
      else
        let s2 := memWrite16 s1 a (s1.regs.get rd).toUInt16
        ({ s2 with regs := s2.regs.set 15 (pc + 4) }, 2)
  | .ldmStm c p u st w l rn mask =>
    if !armCondPass cpsr c then ({ s with regs := s.regs.set 15 (pc + 4) }, 1)
    else
      let xs := regList16 mask
      let n := popcount16 mask
      let base := s.regs.get rn
      let start :=
        if u then (if p then base + 4 else base)
        -- Decrement forms both start at base - 4n (ARM ARM B6.4);
        -- the old DB:+4 term stored one word too high (caught by the
        -- BIOS IRQ stub, whose STMFD/LDMFD pair must round-trip SP).
        else base - w32 (4 * n)
      let wb := if u then base + w32 (4 * n) else base - w32 (4 * n)
      if xs == [] then
        -- empty list: UNPREDICTABLE; mirror the Thumb choice (PC ± 0x40)
        if l then
          let v := memRead32 s start
          let s1 := { s with regs := s.regs.set rn wb }
          let s2 :=
            if st then
              let nspsr := spsrOf s1.regs
              let nt := bitGet32 nspsr 5
              { s1 with regs := { (s1.regs.set 15
                (if nt then v &&& 0xFFFFFFFE else v &&& 0xFFFFFFFC)) with cpsr := nspsr } }
            else fixLoadedPC s1 v
          ({ s2 with regs := s2.regs.set rn wb }, 4)
        else
          let s1 := memWrite32 s start (s.regs.get 15)
          ({ s1 with regs := (s1.regs.set rn wb).set 15 (pc + 4) }, 4)
      else if l then
        let s1 := popRegs s start xs
        let s2 := if !w || xs.contains rn then s1
                  else { s1 with regs := s1.regs.set rn wb }
        -- S + PC: restore CPSR (user-bank forcing deviated: normal transfer)
        if st && xs.contains 15 then
          let nspsr := spsrOf s2.regs
          let nt := bitGet32 nspsr 5
          let v := s2.regs.get 15
          ({ s2 with regs := { (s2.regs.set 15
            (if nt then v &&& 0xFFFFFFFE else v &&& 0xFFFFFFFC)) with cpsr := nspsr } }, n + 3)
        else
          let s3 :=
            if xs.contains 15 then writePC s2 (s2.regs.get 15)
            else { s2 with regs := s2.regs.set 15 (pc + 4) }
          (s3, n + 3)
      else
        let s1 := pushRegs s start xs
        let s2 := if !w then s1 else { s1 with regs := s1.regs.set rn wb }
        ({ s2 with regs := s2.regs.set 15 (pc + 4) }, n + 2)
  | .b c off =>
    if !armCondPass cpsr c then ({ s with regs := s.regs.set 15 (pc + 4) }, 1)
    else
      let tgt : Int := (pc.toNat : Int) + 8 + off
      ({ s with regs := s.regs.set 15 (intToW32 tgt) }, 3)
  | .bl c off =>
    if !armCondPass cpsr c then ({ s with regs := s.regs.set 15 (pc + 4) }, 1)
    else
      let tgt : Int := (pc.toNat : Int) + 8 + off
      ({ s with regs := (s.regs.set 14 (pc + 4)).set 15 (intToW32 tgt) }, 4)
  | .bx c rm =>
    if !armCondPass cpsr c then ({ s with regs := s.regs.set 15 (pc + 4) }, 1)
    else
      let a := s.regs.get rm
      let thumb := (a &&& 1) == 1
      let cpsr := if thumb then bitSet32 s.regs.cpsr 5 else bitClear32 s.regs.cpsr 5
      ({ s with regs := { (s.regs.set 15 (a &&& 0xFFFFFFFE)) with cpsr := cpsr } }, 3)
  | .swi c imm =>
    if !armCondPass cpsr c then ({ s with regs := s.regs.set 15 (pc + 4) }, 1)
    else
      let (sH, takeExc) := hleSwi s imm
      if takeExc then (serviceSwi sH pc, 2)
      else ({ sH with regs := sH.regs.set 15 (pc + 4) }, 2)
  | .swp c b rn rd rm =>
    if !armCondPass cpsr c then ({ s with regs := s.regs.set 15 (pc + 4) }, 1)
    else
      let a := s.regs.get rn
      let (s, tmp) := if b then
          let (s, t) := memRead8E s a; (s, t.toUInt32)
        else memRead32E s a
      let s1 := if b then memWrite8 s a (s.regs.get rm).toUInt8
                else memWrite32 s a (s.regs.get rm)
      ({ s1 with regs := (s1.regs.set rd tmp).set 15 (pc + 4) }, 3)
  | .nop => ({ s with regs := s.regs.set 15 (pc + 4) }, 1)

-- ── Advance: timers + PPU line counter ──

/-- Timer overflow IRQ bit: TM0 → IF.3 … TM3 → IF.6. -/
@[inline] def timerIrqBit : Nat → UInt16
  | 0 => 0x0008 | 1 => 0x0010 | 2 => 0x0020 | _ => 0x0040

/-- Step one timer: `n` bus cycles in, overflow count out (for cascade).
    Count-up channels (1-3, ctrl.2) tick on `tin` overflows from below;
    TM0 ignores count-up (no cascade source). Overflow reloads + sets IF
    (unconditionally, matching the agb-test calibration). -/
def stepTimerCh (s : AGBState) (i n tin : Nat) : AGBState × Nat :=
  let ch := s.timers.ch.getD i {}
  if ((ch.ctrl >>> 7) &&& 1) == 0 then (s, 0)
  else if i != 0 && ((ch.ctrl >>> 2) &&& 1) == 1 then
    if tin == 0 then (s, 0)
    else
      let total := ch.cnt.toNat + tin
      let over := total / 0x10000
      let cnt := if over > 0 then ch.reload else w16 (total % 0x10000)
      let irq := if over > 0 then
          { s.irq with if_ := s.irq.if_ ||| timerIrqBit i } else s.irq
      let tmrs := { ch := s.timers.ch.set! i { ch with cnt := cnt } }
      ({ s with timers := tmrs, irq := irq }, over)
  else
    let div := timerDiv ch.ctrl
    let acc := ch.acc + n
    let ticks := acc / div
    if ticks == 0 then
      ({ s with timers := { ch := s.timers.ch.set! i { ch with acc := acc } } }, 0)
    else
      let total := ch.cnt.toNat + ticks
      let over := total / 0x10000
      let cnt := if over > 0 then ch.reload else w16 (total % 0x10000)
      let irq := if over > 0 then
          { s.irq with if_ := s.irq.if_ ||| timerIrqBit i } else s.irq
      let tmrs := { ch := s.timers.ch.set! i { ch with cnt := cnt, acc := acc % div } }
      ({ s with timers := tmrs, irq := irq }, over)

/-- Component-level timer step: identical arithmetic to `stepTimerCh`
    but threads `(timers, irq)` instead of whole `AGBState`, so fused
    callers (`stepTimers`, `advance`) commit once instead of ~4×. -/
@[inline] def stepTimerChCore (tmrs : AgbTimers) (irq : AgbIrq) (i n tin : Nat) :
    AgbTimers × AgbIrq × Nat :=
  let ch := tmrs.ch.getD i {}
  if ((ch.ctrl >>> 7) &&& 1) == 0 then (tmrs, irq, 0)
  else if i != 0 && ((ch.ctrl >>> 2) &&& 1) == 1 then
    if tin == 0 then (tmrs, irq, 0)
    else
      let total := ch.cnt.toNat + tin
      let over := total / 0x10000
      let cnt := if over > 0 then ch.reload else w16 (total % 0x10000)
      let irq := if over > 0 then
          { irq with if_ := irq.if_ ||| timerIrqBit i } else irq
      ({ ch := tmrs.ch.set! i { ch with cnt := cnt } }, irq, over)
  else
    let div := timerDiv ch.ctrl
    let acc := ch.acc + n
    let ticks := acc / div
    if ticks == 0 then
      ({ ch := tmrs.ch.set! i { ch with acc := acc } }, irq, 0)
    else
      let total := ch.cnt.toNat + ticks
      let over := total / 0x10000
      let cnt := if over > 0 then ch.reload else w16 (total % 0x10000)
      let irq := if over > 0 then
          { irq with if_ := irq.if_ ||| timerIrqBit i } else irq
      ({ ch := tmrs.ch.set! i { ch with cnt := cnt, acc := acc % div } }, irq, over)

/-- Single-channel wrapper agrees with the core (one commit). -/
theorem stepTimerCh_eq_core (s : AGBState) (i n tin : Nat) :
    stepTimerCh s i n tin =
      let (tmrs, irq, o) := stepTimerChCore s.timers s.irq i n tin
      (({ s with timers := tmrs, irq := irq }, o)) := by
  unfold stepTimerCh stepTimerChCore
  simp only []
  repeat (first | split | rfl)

def stepTimers (s : AGBState) (n : Nat) : AGBState :=
  let (t1, q1, o0) := stepTimerChCore s.timers s.irq 0 n 0
  let (t2, q2, o1) := stepTimerChCore t1 q1 1 n o0
  let (t3, q3, o2) := stepTimerChCore t2 q2 2 n o1
  let (t4, q4, _o3) := stepTimerChCore t3 q3 3 n o2
  if o0 == 0 && o1 == 0 then
    { s with timers := t4, irq := q4 }
  else
    let s1 := { s with timers := t4, irq := q4 }
    let s2 := apuTimerOverflow s1 0 o0
    apuTimerOverflow s2 1 o1

/-- Refresh DISPSTAT VBlank (bit0) + VCounter (bit2) flags for `vc`. -/
def dispstatFor (dispstat : UInt16) (vc : Nat) : UInt16 :=
  let vbl : UInt16 := if 160 <= vc && vc < AGB_LINES_PER_FRAME then 1 else 0
  let setting := ((dispstat >>> 8) &&& (0xFF : UInt16)).toNat
  let vct : UInt16 := if vc == setting then 4 else 0
  (dispstat &&& (0xFFF8 : UInt16)) ||| vbl ||| vct

/-- VCounter IRQ: IF.2 when the fresh VCOUNT flag is set and
    DISPSTAT.5 enables it. (HBlank IF.1 needs hpos tracking: open gap.) -/
def stepIrqV (irq : AgbIrq) (dispstat : UInt16) : AgbIrq :=
  if ((dispstat >>> 2) &&& 1) == 1 && ((dispstat >>> 5) &&& 1) == 1 then
    { irq with if_ := irq.if_ ||| 4 }
  else irq

def stepPpu (s : AGBState) (n : Nat) : AGBState :=
  let dots := s.ppu.dots + n
  if dots < AGB_CYCLES_PER_LINE then { s with ppu := { s.ppu with dots := dots } }
  else
    let dots := dots - AGB_CYCLES_PER_LINE
    let vc := s.ppu.vcount.toNat + 1
    if vc == 160 then
      let sD := runVBlankDma s
      let ppu1 := { sD.ppu with dots := dots }
      let ppu2 := { ppu1 with vcount := (160 : UInt16) }
      let disp := dispstatFor s.ppu.dispstat 160
      let ppu3 := { ppu2 with dispstat := disp }
      let irq1 := { sD.irq with if_ := sD.irq.if_ ||| (1 : UInt16) }
      { sD with ppu := ppu3, irq := stepIrqV irq1 disp }
    else if vc >= AGB_LINES_PER_FRAME then
      let ppu1 := { s.ppu with dots := dots }
      let ppu2 := { ppu1 with vcount := (0 : UInt16) }
      let ppu3 := { ppu2 with frame := s.ppu.frame + 1 }
      let disp := dispstatFor s.ppu.dispstat 0
      let ppu4 := { ppu3 with dispstat := disp }
      { s with ppu := ppu4, irq := stepIrqV s.irq disp }
    else
      let ppu1 := { s.ppu with dots := dots }
      let ppu2 := { ppu1 with vcount := w16 vc }
      let disp := dispstatFor s.ppu.dispstat vc
      let ppu3 := { ppu2 with dispstat := disp }
      { s with ppu := ppu3, irq := stepIrqV s.irq disp }

/-- Advance with precomputed registers/bus latch (fast-step tail):
    the common path (no FIFO refill, no PPU line crossing) commits once
    (regs + latch + time); the rare path falls back to the full
    composition with identical values. -/
def advanceOnRegs (s : AGBState) (regs1 : ArmRegs) (busVal : UInt32)
    (n : Nat) : AGBState :=
  let apu1 := apuStepCycles s.apu n
  let (t1, q1, o0) := stepTimerChCore s.timers s.irq 0 n 0
  let (t2, q2, o1) := stepTimerChCore t1 q1 1 n o0
  let (t3, q3, o2) := stepTimerChCore t2 q2 2 n o1
  let (t4, q4, _o3) := stepTimerChCore t3 q3 3 n o2
  let dots := s.ppu.dots + n
  let ppu1 := { s.ppu with dots := dots }
  if o0 == 0 && o1 == 0 && dots < AGB_CYCLES_PER_LINE then
    { s with regs := regs1, busVal := busVal, apu := apu1, timers := t4, irq := q4, ppu := ppu1, cycles := s.cycles + n }
  else
    let s1 := { s with regs := regs1, busVal := busVal, apu := apu1, timers := t4, irq := q4 }
    let s2 := apuTimerOverflow s1 0 o0
    let s3 := apuTimerOverflow s2 1 o1
    let s4 := stepPpu s3 n
    { s4 with cycles := s4.cycles + n }

/-- Canonical advance: APU time, timers (+ sound FIFO/DMA), PPU,
    cycles += n. APU steps first so a batch's samples mix pre-batch
    FIFO state while endpoint pops apply after. -/
def advance (s : AGBState) (n : Nat) : AGBState :=
  advanceOnRegs s s.regs s.busVal n



/-- Cycles until channel `i`'s next prescaler-timer overflow (0 = n/a:
    disabled, or count-up — count-up only ticks on lower-channel
    overflows, and halt jumps are bounded so none can occur inside). -/
def timerOverBoundCh (ch : AgbTimer) (i : Nat) : Nat :=
  if ((ch.ctrl >>> 7) &&& 1) == 0 then 0
  else if i != 0 && ((ch.ctrl >>> 2) &&& 1) == 1 then 0
  else
    let div := timerDiv ch.ctrl
    (0x10000 - ch.cnt.toNat) * div - ch.acc

def timerOverBound (s : AGBState) (i : Nat) : Nat :=
  timerOverBoundCh (s.timers.ch.getD i {}) i

/-- Clamp a jump distance to ≥ 1 (progress guarantee). -/
def jumpClamp (m : Nat) : Nat := if m = 0 then 1 else m

/-- Halt fast-forward distance: cycles to the next PPU line boundary,
    capped by the nearest enabled-timer overflow (0 bound = ignore).
    Jumping is exact: timer overflows, line events, VBlank DMA and the
    IRQs they raise can only land on the endpoint, never inside — and
    the caller re-checks `haltWake` after every jump. Always ≥ 1. -/
def haltJump (s : AGBState) : Nat :=
  let line := AGB_CYCLES_PER_LINE - s.ppu.dots
  let m := line
  let b0 := timerOverBound s 0
  let m := if b0 == 0 then m else min m b0
  let b1 := timerOverBound s 1
  let m := if b1 == 0 then m else min m b1
  let b2 := timerOverBound s 2
  let m := if b2 == 0 then m else min m b2
  let b3 := timerOverBound s 3
  let m := if b3 == 0 then m else min m b3
  jumpClamp m

/-- Halted step with fast-forward: mirrors `stepCPU`'s halted branch
    exactly when a wake is pending, else jumps `haltJump` cycles. -/
def stepHaltJump (s : AGBState) : AGBState :=
  if haltWake s then
    if irqPending s.irq then advance (serviceIrq s) 3
    else advance { s with halted := false } 1
  else advance s (haltJump s)
/-- Slice the fetched halfword from the latched bus word (exact:
    `memRead8` is pure, so `memRead16 s pc` always equals the low or
    high half of `memRead32 s (pc &&& 0xFFFFFFFC)`). -/
def fetchHw (w pc : UInt32) : UInt16 :=
  ((w >>> (if (pc &&& 2) == 0 then 0 else 16)) &&& 0xFFFF).toUInt16

/-- Thumb fast-step core: hot register-only ops + `B` via raw-bit
    dispatch, returning writeback `(regs, cost)` with no state commit.
    Same field extraction and helpers as decode/exec — verified per arm
    by `stepThumbFastCore_*_eq`. -/
def stepThumbFastCore (s : AGBState) (pc : UInt32) (hw : UInt16) :
    Option (ArmRegs × Nat) :=
  let v := hw.toNat
  if v >>> 11 == 0b11100 then
    let off := sx11 (v &&& 0x7FF) * 2
    let tgt : Int := (pc.toNat : Int) + 4 + off
    some (s.regs.set 15 (intToW32 tgt), 3 + memCost s pc 16)
  else if v >>> 11 == 0b00100 then
    let rd := (v >>> 8) &&& 0x7
    let vv := w32 (v &&& 0xFF)
    some (applyNZCVRegs ((s.regs.set rd vv).set 15 (pc + 2))
      { n := bitGet32 vv 31, z := vv == 0, c := cpsrC s.regs.cpsr, v := false },
      1 + memCost s pc 16)
  else if v >>> 11 == 0b00101 then
    let rn := (v >>> 8) &&& 0x7
    let (_, f) := sub32Flags (s.regs.get rn) (w32 (v &&& 0xFF))
    some (applyNZCVRegs (s.regs.set 15 (pc + 2)) f, 1 + memCost s pc 16)
  else if v >>> 11 == 0b00011 && ((v >>> 10) % 2) == 1
      && ((v >>> 9) % 2) == 0 then
    let rd := v &&& 0x7
    let rn := (v >>> 3) &&& 0x7
    let (r, f) := add32Flags (s.regs.get rn) (w32 ((v >>> 6) &&& 0x7))
    some (applyNZCVRegs ((s.regs.set rd r).set 15 (pc + 2)) f,
      1 + memCost s pc 16)
  else if v >>> 11 == 0b00011 && ((v >>> 10) % 2) == 1
      && ((v >>> 9) % 2) == 1 then
    let rd := v &&& 0x7
    let rn := (v >>> 3) &&& 0x7
    let (r, f) := sub32Flags (s.regs.get rn) (w32 ((v >>> 6) &&& 0x7))
    some (applyNZCVRegs ((s.regs.set rd r).set 15 (pc + 2)) f,
      1 + memCost s pc 16)
  else if v >>> 11 == 0b00000 then
    let rd := v &&& 0x7
    let x := s.regs.get ((v >>> 3) &&& 0x7)
    let sh := (v >>> 6) &&& 0x1F
    let r := if sh == 0 then x else x <<< sh.toUInt32
    let c := if sh == 0 then cpsrC s.regs.cpsr else bitGet32 x (32 - sh)
    some (applyNZCVRegs ((s.regs.set rd r).set 15 (pc + 2))
      { n := bitGet32 r 31, z := r == 0, c := c, v := false },
      1 + memCost s pc 16)
  else if v >>> 11 == 0b00001 then
    let rd := v &&& 0x7
    let sh0 := (v >>> 6) &&& 0x1F
    let sh := if sh0 == 0 then 32 else sh0
    let (r, c) := lsrRC (s.regs.get ((v >>> 3) &&& 0x7)) sh (cpsrC s.regs.cpsr)
    some (applyNZCVRegs ((s.regs.set rd r).set 15 (pc + 2))
      { n := bitGet32 r 31, z := r == 0, c := c, v := false },
      1 + memCost s pc 16)
  else if v >>> 11 == 0b00011 && ((v >>> 10) % 2) == 0
      && ((v >>> 9) % 2) == 0 then
    let rd := v &&& 0x7
    let rn := (v >>> 3) &&& 0x7
    let (r, f) := add32Flags (s.regs.get rn) (s.regs.get ((v >>> 6) &&& 0x7))
    some (applyNZCVRegs ((s.regs.set rd r).set 15 (pc + 2)) f,
      1 + memCost s pc 16)
  else if v >>> 11 == 0b00011 && ((v >>> 10) % 2) == 0
      && ((v >>> 9) % 2) == 1 then
    let rd := v &&& 0x7
    let rn := (v >>> 3) &&& 0x7
    let (r, f) := sub32Flags (s.regs.get rn) (s.regs.get ((v >>> 6) &&& 0x7))
    some (applyNZCVRegs ((s.regs.set rd r).set 15 (pc + 2)) f,
      1 + memCost s pc 16)
  else if v >>> 10 == 0b010000 && (((v >>> 6) &&& 0xF == 13) == false) then
    let op := (v >>> 6) &&& 0xF
    let rs := (v >>> 3) &&& 0x7
    let rd := v &&& 0x7
    let (r, f) := aluRes op (s.regs.get rd) (s.regs.get rs) (cpsrC s.regs.cpsr)
    some (applyNZCVRegs ((s.regs.set rd r).set 15 (pc + 2)) f,
      1 + memCost s pc 16)
  else if v >>> 11 == 0b00110 then
    let rd := (v >>> 8) &&& 0x7
    let (r, f) := add32Flags (s.regs.get rd) (w32 (v &&& 0xFF))
    some (applyNZCVRegs ((s.regs.set rd r).set 15 (pc + 2)) f,
      1 + memCost s pc 16)
  else if v >>> 11 == 0b00111 then
    let rd := (v >>> 8) &&& 0x7
    let (r, f) := sub32Flags (s.regs.get rd) (w32 (v &&& 0xFF))
    some (applyNZCVRegs ((s.regs.set rd r).set 15 (pc + 2)) f,
      1 + memCost s pc 16)
  else if v >>> 11 == 0b00010 then
    let rd := v &&& 0x7
    let sh0 := (v >>> 6) &&& 0x1F
    let sh := if sh0 == 0 then 32 else sh0
    let (r, c) := asrRC (s.regs.get ((v >>> 3) &&& 0x7)) sh (cpsrC s.regs.cpsr)
    some (applyNZCVRegs ((s.regs.set rd r).set 15 (pc + 2))
      { n := bitGet32 r 31, z := r == 0, c := c, v := false },
      1 + memCost s pc 16)
  else if v >>> 12 == 0b01101 && (((v >>> 8) &&& 0xF == 14) == false)
      && (((v >>> 8) == 223) == false) then
    let cond := (v >>> 8) &&& 0xF
    let raw := v &&& 0xFF
    let off : Int :=
      if raw < 0x80 then (raw : Int) * 2 else ((raw : Int) - 0x100) * 2
    if condPass s.regs.cpsr cond then
      let tgt : Int := (pc.toNat : Int) + 4 + off
      some ((s.regs.set 15 (intToW32 tgt)), 3 + memCost s pc 16)
    else
      some ((s.regs.set 15 (pc + 2)), 1 + memCost s pc 16)
  else none

/-- Thumb fast step: single-match dispatch over the core, one fused
    commit in the tail. -/
def stepThumbFast (s : AGBState) (pc w : UInt32) (hw : UInt16) :
    Option AGBState :=
  match stepThumbFastCore s pc hw with
  | some (regs1, n) => some (advanceOnRegs s regs1 w n)
  | none => none



/-- One CPU step: halt/IRQ/fetch-decode-exec/advance. Fetch latches the
    prefetch word (open-bus source) and pays fetch waitstates; data
    waitstates come from `execMemCostT/A` alongside the CPU base cost.
    The halfword/word is sliced from the latched bus word (exact:
    `memRead8` is pure, so the bytes coincide). A parked CPU only
    observes masked IRQs (unmasked ones neither wake nor dispatch it —
    HW would run their handlers then re-park, which nets out here;
    documented). -/
def stepCPU (s : AGBState) : AGBState :=
  if s.halted then
    if haltWake s then
      if irqPending s.irq then advance (serviceIrq s) 3
      else advance { s with halted := false } 1
    else advance s 1
  else if irqPending s.irq then
    advance (serviceIrq s) 3
  else if cpsrT s.regs.cpsr then
    let pc := s.regs.pc
    let w := memRead32 s (pc &&& 0xFFFFFFFC)
    match stepThumbFast s pc w (fetchHw w pc) with
    | some s' => s'
    | none =>
      let s := { s with busVal := w }
      let hw := fetchHw w pc
      let ins := decodeThumb hw
      let (s2, c) := execThumb s ins
      advance s2 (c + memCost s pc 16 + execMemCostT s ins)
  else
    let pc := s.regs.pc
    let w := memRead32 s (pc &&& 0xFFFFFFFC)
    let s := { s with busVal := w }
    let w := if (pc &&& 3) == 0 then w else memRead32 s pc
    let ins := decodeArm w
    let (s2, c) := execArm s ins
    advance s2 (c + memCost s pc 32 + execMemCostA s ins)

end AGB
