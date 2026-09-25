/-
  lean-agb — GBA mode CLI (headless-first; windowed SDL arrives in Phase 2).

  Usage:
    lean-agb ROM.gba --headless [--frames 600] [--cycles N] [--dump frame.ppm]
  Without `--headless`, runs 60 frames headless (SDL frontend is Phase 2).
-/
import LeanAGB
import LeanAGB.Sdl.Driver

open AGB
open AGB.Sdl

structure AgbOpts where
  rom : String := ""
  headless : Bool := false
  frames : Nat := 600
  cycles : Nat := 0
  dump : String := ""
  wav : String := ""
  save : String := "auto"
  scale : Nat := 3
  input : String := ""
  bios : String := ""
  tas : String := ""
  debug : Bool := false

def parseAgbArgs : List String → AgbOpts → AgbOpts
  | [], o => o
  | "--headless" :: rest, o => parseAgbArgs rest { o with headless := true }
  | "--frames" :: n :: rest, o => parseAgbArgs rest { o with frames := n.toNat! }
  | "--cycles" :: n :: rest, o => parseAgbArgs rest { o with cycles := n.toNat! }
  | "--dump" :: p :: rest, o => parseAgbArgs rest { o with dump := p }
  | "--dump-wav" :: p :: rest, o => parseAgbArgs rest { o with wav := p }
  | "--save" :: k :: rest, o => parseAgbArgs rest { o with save := k }
  | "--scale" :: n :: rest, o => parseAgbArgs rest { o with scale := n.toNat! }
  | "--input" :: spec :: rest, o => parseAgbArgs rest { o with input := spec }
  | "--bios" :: p :: rest, o => parseAgbArgs rest { o with bios := p }
  | "--tas" :: p :: rest, o => parseAgbArgs rest { o with tas := p }
  | "--debug" :: rest, o => parseAgbArgs rest { o with debug := true }
  | a :: rest, o =>
    if o.rom == "" && !a.startsWith "--" then parseAgbArgs rest { o with rom := a }
    else parseAgbArgs rest o

/-- `--save` name to backup kind (`auto` scans ROM ID strings). -/
def saveKindOf : String → SaveKind
  | "flash64" => .flash64 | "flash128" => .flash128
  | "eeprom4k" => .eeprom4k | "eeprom64k" => .eeprom64k
  | _ => .sram

/-- Button name → poll bit (Right Left Up Down A B Sel Sta, L R). -/
def buttonBit : String → Option Nat
  | "right" => some 0 | "left" => some 1 | "up" => some 2 | "down" => some 3
  | "a" => some 4 | "b" => some 5 | "select" => some 6 | "start" => some 7
  | "l" => some 10 | "r" => some 11
  | _ => none

/-- Parse `btn@start+len,btn@start+len,...` into a script. -/
def parseInput (spec : String) : Array (Nat × Nat × Nat) :=
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

/-- Poll mask held at `frame` by a script. -/
def scriptMask (script : Array (Nat × Nat × Nat)) (frame : Nat) : UInt32 :=
  (script.foldl (fun (acc : Nat) (e : Nat × Nat × Nat) =>
    match e with
    | (b, s, l) => if s <= frame && frame < s + l then acc ||| (1 <<< b) else acc) 0).toUInt32

/-- Strip a trailing CR (CRLF logs), list-based (no `Slice` roundtrip). -/
def stripCR (s : String) : String :=
  let cs := s.toList
  if cs.getLast? == some '\r' then String.ofList cs.dropLast else s

/-- Strip one leading/trailing `|` framing bar, list-based. -/
def stripPipes (s : String) : String :=
  let cs := s.toList
  let cs := if cs.head? == some '|' then cs.tail else cs
  let cs := if cs.getLast? == some '|' then cs.dropLast else cs
  String.ofList cs

/-- One TAS button row → poll mask. BizHawk GBA `Input Log.txt` rows look
    like `|    0,    0,    0,    0,...........|` — four analog fields, then
    one char per button in `LogKey` order
    `Up|Down|Left|Right|Start|Select|B|A|L|R|Power`, where `.` = released
    and any other char = held. Poll-bit mapping follows `buttonBit`
    (Right=0 Left=1 Up=2 Down=3 A=4 B=5 Select=6 Start=7 L=10 R=11);
    Power has no host key and is ignored. -/
def tasRowMask (row : String) : UInt32 :=
  let inner := stripPipes (stripCR row)
  -- button field = text after the last comma (analog fields may pad)
  let parts := inner.splitToList (· == ',')
  let btns := parts.getLastD ""
  let cs := btns.toList
  let held (i : Nat) : Bool :=
    match cs.getD i '.' with
    | '.' => false
    | ' ' => false
    | _ => true
  let b0 := if held 0 then (1 <<< 2) else 0  -- Up
  let b1 := if held 1 then (1 <<< 3) else 0  -- Down
  let b2 := if held 2 then (1 <<< 1) else 0  -- Left
  let b3 := if held 3 then (1 <<< 0) else 0  -- Right
  let b4 := if held 4 then (1 <<< 7) else 0  -- Start
  let b5 := if held 5 then (1 <<< 6) else 0  -- Select
  let b6 := if held 6 then (1 <<< 5) else 0  -- B
  let b7 := if held 7 then (1 <<< 4) else 0  -- A
  let b8 := if held 8 then (1 <<< 10) else 0 -- L
  let b9 := if held 9 then (1 <<< 11) else 0 -- R
  (b0 ||| b1 ||| b2 ||| b3 ||| b4 ||| b5 ||| b6 ||| b7 ||| b8 ||| b9).toUInt32

/-- Parse a full `Input Log.txt` body into per-frame poll masks
    (skips `[Input]`/`LogKey:`/`[/Input]` framing lines). -/
def parseTasLog (body : String) : Array UInt32 :=
  (body.splitToList (· == '\n')).foldl (fun acc line =>
    let t := stripCR line
    if !t.startsWith "|" then acc
    else if (t.splitOn ",").length < 4 then acc
    else if t.startsWith "|LogKey" || t.startsWith "[Input" || t.startsWith "[/Input" then acc
    else acc.push (tasRowMask t)) #[]

/-- Read a TAS input log: a raw `Input Log.txt`, or a `.tasproj` zip
    (BizHawk movie project; `Input Log.txt` is extracted via `unzip -p`,
    falling back to `python3 -c zipfile` when `unzip` is missing). -/
def loadTasMasks (path : System.FilePath) : IO (Array UInt32) := do
  let body ←
    if path.toString.endsWith ".tasproj" then
      let out ← IO.Process.output
        { cmd := "unzip", args := #["-p", path.toString, "Input Log.txt"] }
      if out.exitCode == 0 && out.stdout != "" then pure out.stdout
      else
        let py ← IO.Process.output
          { cmd := "python3", args := #["-c",
            "import sys,zipfile; sys.stdout.write(zipfile.ZipFile(sys.argv[1]).read('Input Log.txt').decode())",
            path.toString] }
        if py.exitCode == 0 && py.stdout != "" then pure py.stdout
        else throw (IO.userError s!"[agb] cannot extract Input Log.txt from {path}")
    else IO.FS.readFile path
  pure (parseTasLog body)

/-- Print a CPU/hardware snapshot for debugging boot/replay hangs. -/
def debugAgb (s : AGBState) : IO Unit := do
  let r := s.regs
  IO.println s!"[dbg] pc={r.pc.toNat} cpsr={r.cpsr.toNat} mode={cpsrMode r.cpsr} T={cpsrT r.cpsr}"
  IO.println s!"[dbg] r0={(r.get 0).toNat} r1={(r.get 1).toNat} r2={(r.get 2).toNat} r3={(r.get 3).toNat} r4={(r.get 4).toNat} r5={(r.get 5).toNat} r6={(r.get 6).toNat} r7={(r.get 7).toNat}"
  IO.println s!"[dbg] r8={(r.get 8).toNat} r9={(r.get 9).toNat} r10={(r.get 10).toNat} r11={(r.get 11).toNat} r12={(r.get 12).toNat} sp={(r.get 13).toNat} lr={(r.get 14).toNat}"
  IO.println s!"[dbg] spsr_svc={r.spsr_svc.toNat} spsr_irq={r.spsr_irq.toNat} sp_svc={r.r13_svc.toNat} lr_svc={r.r14_svc.toNat} sp_irq={r.r13_irq.toNat} lr_irq={r.r14_irq.toNat}"
  IO.println s!"[dbg] halted={s.halted} waitMask={s.waitMask.toNat} ie={s.irq.ie.toNat} if={s.irq.if_.toNat} ime={s.irq.ime} frame={s.ppu.frame} vcount={s.ppu.vcount.toNat} dispcnt={s.ppu.dispcnt.toNat} dispstat={s.ppu.dispstat.toNat} key={s.key.input.toNat}"
  for i in List.range 4 do
    let ch := s.timers.ch.getD i {}
    IO.println s!"[tmr {i}] cnt={ch.cnt.toNat} reload={ch.reload.toNat} ctrl={ch.ctrl.toNat} acc={ch.acc}"
  for i in List.range 4 do
    let d := s.dma.ch.getD i {}
    IO.println s!"[dma {i}] sad={d.sad.toNat} dad={d.dad.toNat} cnt_l={d.cnt_l.toNat} cnt_h={d.cnt_h.toNat}"
  IO.println s!"[dbg] apuStatus={apuStatus s.apu |>.toNat} fifoA={fifoSize s.apu.fifoA} fifoB={fifoSize s.apu.fifoB}"
  -- PC samples over the next 400 instructions (spin vs wander)
  let rec loop : AGBState → Nat → List Nat → List Nat
    | _, 0, acc => acc.reverse
    | st, k + 1, acc =>
      let st := stepCPU st
      loop st k (if k % 40 == 0 then st.regs.pc.toNat :: acc else acc)
  IO.println s!"[dbg] PC samples: {loop s 400 []}"

/-- Headless frames driven by per-frame poll masks (TAS replay), draining
    emitted audio per frame (accumulated by the caller). -/
def runFramesMasks : AGBState → Nat → Nat → Array UInt32 →
    Array ByteArray → AGBState × Array ByteArray
  | s, _, 0, _, ab => (s, ab)
  | s, f, k + 1, masks, ab =>
    let s := runFrame (setButtons s (masks.getD f 0))
    let (apu, out) := apuDrain s.apu
    runFramesMasks { s with apu := apu } (f + 1) k masks (ab.push out)

/-- Headless frames with scripted input applied per frame, draining
    emitted audio per frame (accumulated by the caller). -/
def runFramesInput : AGBState → Nat → Nat → Array (Nat × Nat × Nat) →
    Array ByteArray → AGBState × Array ByteArray
  | s, _, 0, _, ab => (s, ab)
  | s, f, k + 1, sc, ab =>
    let s := runFrame (setButtons s (scriptMask sc f))
    let (apu, out) := apuDrain s.apu
    runFramesInput { s with apu := apu } (f + 1) k sc (ab.push out)

/-- Queue watermarks (bytes of 32768 Hz stereo) for audio-clock
    pacing: below LOW the device is starving (skip all delay, catch
    up now); above HIGH we're ahead (double the deadline delay to
    bleed surplus instead of trimming it); between, deadline pacing.
    Hysteresis prevents hunting. -/
def audioLowMark : Nat := 6000
def audioHighMark : Nat := 20000

def s16leAt (b : ByteArray) (o : Nat) : Int :=
  let u := (bget b o).toNat + (bget b (o + 1)).toNat * 256
  if u >= 32768 then (u : Int) - 65536 else u

/-- Stretch stereo s16 so it lasts `elapsedMs` instead of its native
    32768 Hz duration. A frame costs ~25 ms here and only carries
    ~17 ms of audio; played back raw, the device underruns and the
    silence between chunks is a frame-rate buzz. Linear stretch fills
    that gap. No stretch when the frame was on time, and never more
    than 2× (a hitch must not turn one chunk into a drone). -/
def stretchIfSlow (src : ByteArray) (elapsedMs : Nat) : ByteArray :=
  let n := src.size / 4
  let nativeMs := n * 1000 / 32768
  if n < 2 || nativeMs == 0 || elapsedMs <= nativeMs + 1 then src
  else
    let elapsed := min elapsedMs (nativeMs * 2)
    let m := n * elapsed / nativeMs
    if m <= n then src
    else
      let rec go : Nat → ByteArray → ByteArray
        | 0, acc => acc
        | k + 1, acc =>
          let i := m - (k + 1)
          let den := m - 1
          let idx := i * (n - 1) / den
          let frac := i * (n - 1) % den
          let i1 := min (idx + 1) (n - 1)
          let lerp (a b : Int) : Int := a + (b - a) * (frac : Int) / (den : Int)
          let l := lerp (s16leAt src (idx * 4)) (s16leAt src (i1 * 4))
          let r := lerp (s16leAt src (idx * 4 + 2)) (s16leAt src (i1 * 4 + 2))
          go k (pushS16LE (pushS16LE acc l) r)
      go m (ByteArray.emptyWithCapacity (m * 4 + 16))

/-- Windowed run: one emulated frame per host frame, throttled.
    F1 (edge-triggered) writes `snapN.ppm` framebuffer dumps.
    Video is best-effort: frames past their deadline skip presenting
    (at most 3 in a row, so video never drops below ~15fps) while
    audio pushes every emulated frame — emulation stays exact, only
    presentation drops. Delay is audio-clocked (see watermarks above),
    so oversleep can't accumulate lateness. Partial: runs until the
    user quits (or SDL is unavailable). -/

partial def agbWindowLoop (s : AGBState) (m : RenderMemo) (nextDue frac : Nat)
    (prevF1 snaps skips : Nat) (alive : Bool) (prevFrame : Nat) : IO AGBState := do
  let mask ← poll
  if mask / 256 % 2 == 1 then pure s  -- quit requested
  else
    let t0 ← ticksMs
    let f1 := (mask / 512 % 2).toNat
    let snaps ←
      if f1 == 1 && prevF1 == 0 then do
        let tag := s!"snap{snaps}.ppm"
        dumpPPM s tag
        IO.FS.writeBinFile (tag ++ ".state") (dumpRenderState s)
        IO.println s!"[agb] snapshot {tag} written (frame {s.ppu.frame})"
        pure (snaps + 1)
      else pure snaps
    let s := setButtons s mask
    let s := runFrame s
    let now ← ticksMs
    let skip := nextDue < now.toNat && skips < 3
    let (s, m, skips) ←
      if skip then pure (s, m, skips + 1)
      else do
        let (s, m) ← presentAgbFrame s m
        pure (s, m, 0)
    let (apu, abuf) := apuDrain s.apu
    let pushed ← ticksMs
    let elapsed := (pushed - t0).toNat
    audioPush (stretchIfSlow abuf elapsed)
    let s := { s with apu := apu }
    let (due, frac) := nextDeadline nextDue frac
    let q ← audioQueued
    -- Audio-clock pacing (self-correcting, unlike pure deadline pacing
    -- whose delay oversleep can only ever run late): catch up while the
    -- device starves, coast past the deadline while ahead. The `alive`
    -- latch keeps deadline pacing when no audio device exists at all
    -- (queue reads constant 0 there).
    let alive := alive || q.toNat != 0
    let base := if due > now.toNat then due - now.toNat else 0
    let d :=
      if !alive then base
      else if q.toNat < audioLowMark then 0
      else if q.toNat > audioHighMark then base * 2
      else base
    if d != 0 then
      delayMs d.toUInt32
    -- Heartbeat: progress + audio health every 60 frames, so a slow
    -- run is distinguishable from a hung one (stdout is block-buffered
    -- to files; the window itself always shows the latest frame).
    if s.ppu.frame % 60 == 0 && s.ppu.frame != prevFrame then
      IO.println s!"[agb] frame={s.ppu.frame} pc={s.regs.pc.toNat} queued={q.toNat}B skips={skips}"
    agbWindowLoop s m due frac f1 snaps skips alive s.ppu.frame

def runWindowed (s0 : AGBState) (scale : Nat) (savPath : System.FilePath) : IO Unit := do
  let rc ← openWindow scale.toUInt32
  if rc != 0 then
    IO.println s!"[agb] SDL unavailable (code {rc}); falling back to 60 headless frames."
  else
    IO.println "[agb] arrows = d-pad, X = A, Z = B, Q = L, W = R, Enter = Start, RShift = Select"
  let t0 ← ticksMs
  let send ←
    if rc != 0 then pure (runFrames s0 60)
    else agbWindowLoop s0 {} t0.toNat 0 0 0 0 false 0
  close
  if (saveGame send).size != 0 then
    IO.FS.writeBinFile savPath (saveGame send)
  IO.println s!"[agb] done. cycles={send.cycles} pc={send.regs.pc.toNat}"

/-- Write accumulated stereo s16LE @32768 Hz as a WAV file. -/
def writeWav (path : System.FilePath) (data : ByteArray) : IO Unit := do
  let n := data.size
  let ascii (s : String) : Array UInt8 :=
    s.toList.toArray.map (fun c => w8 c.toNat)
  let h := ByteArray.mk (ascii "RIFF")
  let h := pushU32LE h (36 + n).toUInt32
  let h := h ++ ByteArray.mk (ascii "WAVEfmt ")
  let h := pushU32LE h 16
  let h := pushU16LE h 1
  let h := pushU16LE h 2
  let h := pushU32LE h 32768
  let h := pushU32LE h (32768 * 4)
  let h := pushU16LE h 4
  let h := pushU16LE h 16
  let h := h ++ ByteArray.mk (ascii "data")
  let h := pushU32LE h n.toUInt32
  IO.FS.writeBinFile path (h ++ data)

/-- Peak |sample| over stereo s16LE bytes (mix health check). -/
def wavPeak (data : ByteArray) : Nat :=
  (List.range (data.size / 4)).foldl (fun acc i =>
    let lo := (bget data (i * 4)).toNat
    let hi := (bget data (i * 4 + 1)).toNat
    let v : Int :=
      if hi >= 128 then (lo : Int) + (hi : Int) * 256 - 65536
      else (lo : Int) + (hi : Int) * 256
    Nat.max acc v.natAbs) 0

def main (args : List String) : IO Unit := do
  let o := parseAgbArgs args {}
  if o.rom == "" then
    IO.println "usage: lean-agb ROM.gba [--scale N] [--headless --frames N --dump f.ppm --dump-wav f.wav --input ...] [--cycles N] [--save auto|sram|flash64|flash128|eeprom4k|eeprom64k] [--bios gba_bios.bin] [--tas movie.tasproj] [--debug]"
  else do
    let bytes ← IO.FS.readBinFile o.rom
    let kind := if o.save == "auto" then detectSaveKind bytes else saveKindOf o.save
    -- Real-BIOS boot when `--bios` is given (reset vector, ARM/SVC,
    -- PC = 0); otherwise the direct-boot HLE path. TAS movies recorded
    -- with `SkipBios = false` must pair with `--bios`.
    let biosBytes ←
      if o.bios == "" then pure ByteArray.empty
      else IO.FS.readBinFile o.bios
    let s0 :=
      if biosBytes.size == 0 then AGBState.freshAuto bytes kind
      else AGBState.freshBiosBoot bytes biosBytes kind
    IO.println s!"[agb] rom bytes={bytes.size} save={repr kind} arm={bootIsArm bytes} bios={(if biosBytes.size == 0 then "hle stub (direct boot)" else s!"{biosBytes.size}B reset-vector boot")}"
    let savPath : System.FilePath := o.rom ++ ".sav"
    let sav ← try IO.FS.readBinFile savPath catch _ => pure ByteArray.empty
    let s0 := loadGame s0 sav
    if o.headless then
      let script := parseInput o.input
      if o.cycles != 0 then
        let send := runUntilCycles s0 o.cycles
        let (_, abuf) := apuDrain send.apu
        if o.wav != "" then
          writeWav o.wav abuf
        if o.dump != "" then
          dumpPPM send o.dump
        if (saveGame send).size != 0 then
          IO.FS.writeBinFile savPath (saveGame send)
        IO.println s!"[agb] cycles={send.cycles} frame={send.ppu.frame} pc={send.regs.pc.toNat} vcount={send.ppu.vcount.toNat} if={send.irq.if_.toNat}"
        if o.debug then debugAgb send
      else if o.tas != "" then
        let masks ← loadTasMasks o.tas
        -- Default `--frames 600` means "the whole movie"; an explicit
        -- `--frames N` caps (or pads with released) the replay.
        let n := if o.frames == 600 then masks.size else o.frames
        IO.println s!"[agb] tas frames={masks.size} replaying={n}"
        let (send, chunks) := runFramesMasks s0 0 n masks #[]
        let abuf := chunks.foldl (fun acc c => acc ++ c) ByteArray.empty
        if o.wav != "" then
          writeWav o.wav abuf
        if o.dump != "" then
          dumpPPM send o.dump
        if (saveGame send).size != 0 then
          IO.FS.writeBinFile savPath (saveGame send)
        IO.println s!"[agb] frames+={send.ppu.frame - s0.ppu.frame} cycles={send.cycles} pc={send.regs.pc.toNat} vcount={send.ppu.vcount.toNat} if={send.irq.if_.toNat} audio={abuf.size}B peak={wavPeak abuf}"
      else
        let (send, chunks) := runFramesInput s0 0 o.frames script #[]
        let abuf := chunks.foldl (fun acc c => acc ++ c) ByteArray.empty
        if o.wav != "" then
          writeWav o.wav abuf
        if o.dump != "" then
          dumpPPM send o.dump
        if (saveGame send).size != 0 then
          IO.FS.writeBinFile savPath (saveGame send)
        IO.println s!"[agb] frames+={send.ppu.frame - s0.ppu.frame} cycles={send.cycles} pc={send.regs.pc.toNat} vcount={send.ppu.vcount.toNat} if={send.irq.if_.toNat} audio={abuf.size}B peak={wavPeak abuf}"
    else
      runWindowed s0 o.scale savPath
