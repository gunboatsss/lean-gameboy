/-
  LeanGameboy.Emu — headless emulation driver: instruction batches,
  frame stepping, ROM loading, save files.
-/
import LeanGameboy.Bus
import LeanGameboy.Framebuffer

namespace GB

/-- Load a ROM image into fresh state. -/
def loadROM (bytes : ByteArray) : GBState :=
  GBState.fresh bytes

/-- Run `n` instructions (fuel-limited). -/
def runInstrs : GBState → Nat → GBState
  | s, 0 => s
  | s, k + 1 => runInstrs (stepCPU s) k

/-- Run until the frame counter changes (i.e. one full frame), with a
    generous instruction cap to avoid hanging on halted states. -/
def runFrame (s : GBState) : GBState :=
  let target := s.ppu.frame + 1
  let rec loop : GBState → Nat → GBState
    | st, 0 => st
    | st, k + 1 =>
      if st.ppu.frame >= target then st
      else loop (stepCPU st) k
  loop s 200000

/-- Run `n` frames. -/
def runFrames : GBState → Nat → GBState
  | s, 0 => s
  | s, k + 1 => runFrames (runFrame s) k

/-- Scripted input entry: (button bit 0..7 = R L U D A B Sel Sta,
    start frame, hold length in frames). -/
abbrev InputScript := Array (Nat × Nat × Nat)

/-- Button mask held at a given frame. -/
def maskAt (script : InputScript) (frame : Nat) : Nat :=
  script.foldl (fun acc p =>
    if p.2.1 <= frame && frame < p.2.1 + p.2.2 then acc ||| (1 <<< p.1)
    else acc) 0

/-- Run `frames` frames, applying `applyInput joy mask` before each frame. -/
def runScript (s : GBState) (frames : Nat) (script : InputScript)
    (applyInput : JoypadState → Nat → JoypadState) : GBState :=
  let rec loop : GBState → Nat → Nat → GBState
    | st, 0, _ => st
    | st, k + 1, f =>
      let st := setButtons st (applyInput st.joy (maskAt script f))
      loop (runFrame st) k (f + 1)
  loop s frames 0

/-- Blargg-style serial output as a string (0x0A-terminated protocol). -/
def serialText (s : GBState) : String :=
  String.ofList (s.serial.out.toList.filterMap fun b =>
    if b == 0 then none else some (Char.ofNat b.toNat))

/-- Run up to `frames` frames, stopping early once the serial log
    contains "Passed" or "Failed" (Blargg protocol). Checks every
    300 frames to amortize the string scan. -/
def runUntilSerial (s : GBState) (frames : Nat) (script : InputScript)
    (applyInput : JoypadState → Nat → JoypadState) : GBState :=
  let rec loop : GBState → Nat → Nat → GBState
    | st, 0, _ => st
    | st, k + 1, f =>
      let st := setButtons st (applyInput st.joy (maskAt script f))
      let st := runFrame st
      if (f + 1) % 300 == 0 then
        let t := serialText st
        if (t.splitOn "Passed").length > 1 || (t.splitOn "Failed").length > 1 then st
        else loop st k (f + 1)
      else loop st k (f + 1)
  loop s frames 0

/-- Run until `cycles` more M-cycles have elapsed (for LCD-off test
    ROMs where no frame boundary ever arrives). Every `stepCPU`
    advances `cycles` by ≥ 1, so fuel `cycles + 1000` always suffices.
    Checks serial for Passed/Failed every 50000 steps. -/
def runUntilCycles (s : GBState) (cycles : Nat) : GBState :=
  let target := s.cycles + cycles
  let rec loop : GBState → Nat → Nat → GBState
    | st, 0, _ => st
    | st, f + 1, k =>
      if target <= st.cycles then st
      else
        let st := stepCPU st
        if k % 50000 == 0 then
          let t := serialText st
          if (t.splitOn "Passed").length > 1 || (t.splitOn "Failed").length > 1 then st
          else loop st f (k + 1)
        else loop st f (k + 1)
  loop s (cycles + 1000) 0

/-- Dump the current framebuffer to a P6 PPM file. -/
def dumpPPM (s : GBState) (path : System.FilePath) : IO Unit :=
  IO.FS.writeBinFile path (fbToPPM s.fb)

/-- Save battery RAM (`.sav` next to the ROM): raw concatenation of banks. -/
def saveRAM (s : GBState) (path : System.FilePath) : IO Unit := do
  let mut bytes := ByteArray.empty
  for b in s.ram.banks do
    bytes := bytes ++ b
  if bytes.size == 0 then pure () else IO.FS.writeBinFile path bytes

/-- Load battery RAM back into state (truncates/pads per bank). -/
def loadRAM (s : GBState) (bytes : ByteArray) : GBState :=
  if bytes.size == 0 then s
  else
    let banks := s.ram.banks.size
    if banks == 0 then s
    else
      let per := bytes.size / banks
      let nbanks := (List.range banks).foldl (fun acc i =>
        let slice := bytes.extract (i * per) ((i + 1) * per)
        acc.push slice) #[]
      { s with ram := { banks := nbanks } }

end GB
