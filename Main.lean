/-
  lean-gameboy — DMG emulator CLI.

  Usage:
    lean-gameboy ROM.gb [--scale 3] [--mute]
    lean-gameboy ROM.gb --headless [--frames 600] [--dump frame.ppm]
-/
import LeanGameboy
import LeanGameboy.Sdl.Driver

open GB
open GB.Sdl

/-- Parsed CLI options. -/
structure Opts where
  rom : String := ""
  scale : Nat := 3
  mute : Bool := false
  headless : Bool := false
  frames : Nat := 600
  cycles : Nat := 0
  dump : String := ""
  input : String := ""
  debug : Bool := false

def parseArgs : List String → Opts → Opts
  | [], o => o
  | "--scale" :: n :: rest, o => parseArgs rest { o with scale := n.toNat! }
  | "--mute" :: rest, o => parseArgs rest { o with mute := true }
  | "--headless" :: rest, o => parseArgs rest { o with headless := true }
  | "--frames" :: n :: rest, o => parseArgs rest { o with frames := n.toNat! }
  | "--cycles" :: n :: rest, o => parseArgs rest { o with cycles := n.toNat! }
  | "--dump" :: p :: rest, o => parseArgs rest { o with dump := p }
  | "--input" :: spec :: rest, o => parseArgs rest { o with input := spec }
  | "--debug" :: rest, o => parseArgs rest { o with debug := true }
  | a :: rest, o =>
    if o.rom == "" && !a.startsWith "--" then parseArgs rest { o with rom := a }
    else parseArgs rest o

/-- Button name → bit (R L U D A B Sel Sta). -/
def buttonBit : String → Option Nat
  | "right" => some 0 | "left" => some 1 | "up" => some 2 | "down" => some 3
  | "a" => some 4 | "b" => some 5 | "select" => some 6 | "start" => some 7
  | _ => none

/-- Parse `btn@start+len,btn@start+len,...` into an `InputScript`. -/
def parseInput (spec : String) : InputScript :=
  if spec == "" then #[]
  else
    (spec.splitToList (· == ',')).foldl (fun acc entry =>
      match entry.splitToList (· == '@') with
      | [name, rest] =>
        match rest.splitToList (· == '+') with
        | [ss, ls] =>
          match buttonBit name with
          | some b => acc.push (b, ss.toNat!, ls.toNat!)
          | none => acc
        | _ => acc
      | _ => acc) #[]

/-- Windowed run: one emulated frame per host frame, throttled.
    Partial: runs until the user quits (or SDL is unavailable). -/
partial def windowLoop (s : GBState) (nextDue : Nat) (mute : Bool) : IO GBState := do
  let mask ← poll
  if mask / 256 % 2 == 1 then pure s  -- quit requested
  else
    let s := setButtons s (buttonsOf s.joy mask)
    let s := runFrame s
    let s ← presentFrame s mute
    let now ← ticksMs
    let due := nextDue + frameMs.toNat
    if due > now.toNat then
      delayMs (due - now.toNat).toUInt32
    windowLoop s due mute

def runWindowed (s0 : GBState) (scale : Nat) (mute : Bool) (savPath : System.FilePath) : IO Unit := do
  let rc ← openWindow scale.toUInt32
  if rc != 0 then
    IO.println s!"[gb] SDL unavailable (code {rc}); falling back to 60 headless frames."
  else
    IO.println "[gb] arrows = d-pad, X = A, Z = B, Enter = Start, RShift = Select"
  let t0 ← ticksMs
  let send ←
    if rc != 0 then pure (runFrames s0 60)
    else windowLoop s0 t0.toNat mute
  close
  saveRAM send savPath
  IO.println s!"[gb] done. cycles={send.cycles} serial={serialText send}"

/-- Cycle-based runner with stderr progress reports (for long test
    ROM runs; survives timeouts since stderr is unbuffered). -/
partial def runUntilCyclesIO (s0 : GBState) (cycles : Nat) (progressEvery : Nat) : IO GBState := do
  let target := s0.cycles + cycles
  let rec loop : GBState → Nat → IO GBState
    | st, k =>
      if target <= st.cycles then pure st
      else
        let st := stepCPU st
        if k % 50000 == 0 then
          let t := serialText st
          if (t.splitOn "Passed").length > 1 || (t.splitOn "Failed").length > 1 then pure st
          else do
            -- step-based heartbeat: advances even if cycles crawl,
            -- distinguishing a true hang from CPU starvation
            if progressEvery != 0 && k % 5000000 == 0 then
              let n := t.length
              IO.eprintln s!"[progress] steps={k} cycles={st.cycles} pc={st.regs.pc.toNat} ly={st.ppu.ly.toNat} apu={st.apu.powered} samples={st.apu.samples.size} sout={st.serial.out.size} tail={t.drop (n - min 60 n)}"
            loop st (k + 1)
        else loop st (k + 1)
  loop s0 0

/-- Two-digit hex for debug dumps. -/
def hex2 (v : UInt8) : String :=
  let h : Nat → Char
    | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4' | 5 => '5'
    | 6 => '6' | 7 => '7' | 8 => '8' | 9 => '9' | 10 => 'a' | 11 => 'b'
    | 12 => 'c' | 13 => 'd' | 14 => 'e' | _ => 'f'
  String.ofList [h (v.toNat / 16), h (v.toNat % 16)]

/-- Print a CPU/hardware snapshot for debugging soft-locks. -/
def debugState (s : GBState) : IO Unit := do
  let r := s.regs
  IO.println s!"[dbg] AF={r.af.toNat} BC={r.bc.toNat} DE={r.de.toNat} HL={r.hl.toNat} SP={r.sp.toNat} PC={r.pc.toNat} IME={r.ime} halted={r.halted}"
  IO.println s!"[dbg] IE={s.ie.toNat} IF={s.if_.toNat} LY={s.ppu.ly.toNat} LCDC={s.ppu.lcdc.toNat} STAT={s.ppu.stat.toNat} DIV={s.timer.div.toNat} TIMA={s.timer.tima.toNat} TAC={s.timer.tac.toNat}"
  let p := s.ppu
  IO.println s!"[ppu] scx={p.scx.toNat} scy={p.scy.toNat} wx={p.wx.toNat} wy={p.wy.toNat} bgp={p.bgp.toNat} obp0={p.obp0.toNat} obp1={p.obp1.toNat} lyc={p.lyc.toNat} mode={p.mode}"
  -- OAM entries with nonzero Y (potentially visible sprites)
  for i in List.range 40 do
    let y := (bget s.oam (i * 4)).toNat
    if y != 0 then
      IO.println s!"[oam {i}] y={y} x={(bget s.oam (i * 4 + 1)).toNat} tile={(bget s.oam (i * 4 + 2)).toNat} attr={(bget s.oam (i * 4 + 3)).toNat}"
  -- WRAM + HRAM hex dump (diff across runs to see if input registers)
  for base in List.range 512 do
    let mut line := ""
    for k in List.range 16 do
      line := line ++ hex2 (bget s.wram (base * 16 + k))
    IO.println s!"[wram {base}] {line}"
  let mut hline := ""
  for k in List.range 127 do
    hline := hline ++ hex2 (bget s.hram k)
  IO.println s!"[hram] {hline}"
  let mapBase := if bitGet p.lcdc 3 then 0x1C00 else 0x1800
  for row in List.range 18 do
    let mut line := s!"[map {row}]"
    for col in List.range 20 do
      let v := bget s.vram (mapBase + row * 32 + col)
      line := line ++ s!" {v.toNat}"
    IO.println line
  -- raw bytes of selected tiles (signed addressing per LCDC.4)
  let signed := !bitGet p.lcdc 4
  for tid in ([10, 11, 14, 25, 29, 34, 37, 88, 91, 113, 114, 116, 120, 121, 122, 171] : List Nat) do
    -- replicate Ppu.tileAddr exactly (Int math for signed half)
    let tbase : Nat :=
      if signed then
        (((0x1000 : Int) + ((tid : Int) - (if tid >= 128 then 256 else 0)) * 16).toNat) % 0x2000
      else tid * 16
    let mut line := s!"[tile {tid}]"
    for k in List.range 16 do
      line := line ++ s!" {(bget s.vram (tbase + k)).toNat}"
    IO.println line
  let op := busRead s r.pc
  if op == 0xCB then
    IO.println s!"[dbg] @PC: CB {(busRead s (r.pc + 1)).toNat} → {repr (Instr.decodeCB (busRead s (r.pc + 1)))}"
  else
    IO.println s!"[dbg] @PC: {op.toNat} {(busRead s (r.pc + 1)).toNat} {(busRead s (r.pc + 2)).toNat} → {repr (Instr.decodeFull op)}"
  -- PC samples over the next 500 instructions (spin vs wander)
  let rec loop : GBState → Nat → List Nat → List Nat
    | st, 0, acc => acc.reverse
    | st, k + 1, acc =>
      let st := stepCPU st
      loop st k (if k % 50 == 0 then st.regs.pc.toNat :: acc else acc)
  IO.println s!"[dbg] PC samples: {loop s 500 []}"
  -- dynamic trace: next 60 instructions with decode
  let rec trace : GBState → Nat → List String → List String
    | _, 0, acc => acc.reverse
    | st, k + 1, acc =>
      let pc := st.regs.pc
      let op := busRead st pc
      let d :=
        if op == 0xCB then s!"{pc.toNat}: CB {(busRead st (pc + 1)).toNat}"
        else s!"{pc.toNat}: {op.toNat} ({repr (Instr.decodeFull op)})"
      trace (stepCPU st) k (d :: acc)
  for l in trace s 60 [] do IO.println s!"[tr] {l}"

def main (args : List String) : IO Unit := do
  let o := parseArgs args {}
  if o.rom == "" then
    IO.println "usage: lean-gameboy ROM.gb [--scale N] [--mute] [--headless --frames N --dump f.ppm]"
  else do
    let romPath : System.FilePath := o.rom
    let bytes ← IO.FS.readBinFile romPath
    let h := parseHeader bytes
    IO.println s!"[gb] {h.title} type={h.cartType.toNat} mbc={repr h.mbc} romBanks={h.romBanks} ramBanks={h.ramBanks} checksumOk={h.headerChecksumOk} logoOk={logoOk bytes}"
    let s0 := loadROM bytes
    let savPath : System.FilePath := o.rom ++ ".sav"
    -- load an existing .sav if present (ignore errors)
    let sav ← try IO.FS.readBinFile savPath catch _ => pure ByteArray.empty
    let s0 := loadRAM s0 sav
    if o.headless then
      let script := parseInput o.input
      let send ←
        if o.cycles != 0 then runUntilCyclesIO s0 o.cycles 2000000
        else pure (runUntilSerial s0 o.frames script
          (fun joy mask => buttonsOf joy mask.toUInt32))
      if o.dump != "" then
        dumpPPM send o.dump
      saveRAM send savPath
      IO.println s!"[gb] frames={o.frames} cycles={send.cycles} LY={send.ppu.ly} serial={serialText send}"
      if o.debug then debugState send
    else
      runWindowed s0 o.scale o.mute savPath
