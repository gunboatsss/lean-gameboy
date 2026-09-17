/-
  gb-bench — subsystem microbenchmarks + full-frame timing.

  Usage: gb-bench ROM.gb [frames]
  Isolates render / APU / timer / core costs to guide optimization.
-/
import LeanGameboy

open GB

def msNow : IO Nat := IO.monoMsNow

def bench (name : String) (n : Nat) (f : Nat → IO Unit) : IO Nat := do
  let t0 ← msNow
  let rec loop : Nat → IO Unit
    | 0 => pure ()
    | k + 1 => f k >>= fun _ => loop k
  loop n
  let t1 ← msNow
  let dt := t1 - t0
  IO.println s!"[bench] {name}: {dt}ms for {n} iters ({dt * 1000000 / n}ns/iter)"
  pure dt

def main (args : List String) : IO Unit := do
  let rom := if args.length > 0 then args[0]! else "Tetris (JUE) (V1.1) [!].gb"
  let frames := if args.length > 1 then args[1]!.toNat! else 120
  let bytes ← IO.FS.readBinFile rom
  let s0 := loadROM bytes
  -- warm up into gameplay-ish state (title reached, APU may be on)
  let s1 := runFrames s0 950
  IO.println s!"[bench] warmed to frame {s1.ppu.frame}, apuPowered={s1.apu.powered}"
  -- 1. full frames (nanosecond clock; the println forces eval before t1)
  let t0 ← IO.monoNanosNow
  let s2 := runFrames s1 frames
  IO.println s!"[bench] full: cycles={s2.cycles - s1.cycles} for {frames} frames"
  let t1 ← IO.monoNanosNow
  IO.println s!"[bench] full: {(t1 - t0) / 1000}us total ({(t1 - t0) / 1000 / frames}us/frame)"
  -- 2. renderer in isolation (typical in-game VRAM/OAM)
  let vram := s2.vram
  let oam := s2.oam
  let ppu := s2.ppu
  let acc ← IO.mkRef 0
  let _ ← bench "renderLine x1440" 1440 (fun i => do
    let pr := { ppu with ly := w8 (i % 144) }
    let line := PpuState.renderLine pr vram oam
    acc.modify (· + line.size))
  IO.println s!"[bench] (acc={← acc.get})"
  -- 3. APU step with music-like state
  let apu0 : ApuState :=
    { ({} : ApuState) with
      powered := true
      nr50 := 0x77
      nr51 := 0xFF
      ch1 := { ({} : PulseCh) with enable := true, dac := true, freq := 1000, vol := 8, duty := 2 }
      ch2 := { ({} : PulseCh) with enable := true, dac := true, freq := 500, vol := 6, duty := 1 }
      ch4 := { ({} : NoiseCh) with enable := true, dac := true, vol := 4 } }
  let aref ← IO.mkRef apu0
  let _ ← bench "apu.step(3) x20000" 20000 (fun _ => do
    aref.modify (·.step 3))
  IO.println s!"[bench] apu samples accrued={(← aref.get).samples.size}"
  -- sharing probe: same stepping against a pre-grown 1MB buffer
  let big : ApuState :=
    { apu0 with samples := ByteArray.mk (Array.mk (List.replicate 1000000 0)) }
  let bigref ← IO.mkRef big
  let _ ← bench "apu.step(3) x2000 BIGBUF" 2000 (fun _ => do
    bigref.modify (·.step 3))
  IO.println s!"[bench] bigbuf end size={(← bigref.get).samples.size}"
  -- 4. timer step
  let tmref ← IO.mkRef ({ tac := 0x05 } : TimerState)
  let _ ← bench "timer.step(3) x200000" 200000 (fun _ => do
    tmref.modify (·.step 3))
  IO.println s!"[bench] timer tima={(← tmref.get).tima}"
  -- 5. raw stepCPU on live state
  let stref ← IO.mkRef s2
  let _ ← bench "stepCPU x100000" 100000 (fun _ => do
    stref.modify stepCPU)
  let st ← stref.get
  IO.println s!"[bench] pc={st.regs.pc.toNat} cycles+={st.cycles - s2.cycles}"
  -- 6. windowed present path (blit + audio + present), if SDL opens
  let rc ← GB.Sdl.openWindow 2
  IO.println s!"[bench] sdl open rc={rc}"
  if rc == 0 then
    let t0 ← IO.monoNanosNow
    let rec ploop : GBState → Nat → IO GBState
      | s, 0 => pure s
      | s, k + 1 => do
        let s ← GB.Sdl.presentFrame s false
        ploop s k
    let s3 ← ploop s2 120
    IO.println s!"[bench] presented 120 frames (drained={(← pure s3.apu.samples.size)})"
    let t1 ← IO.monoNanosNow
    IO.println s!"[bench] present: {(t1 - t0) / 1000 / 120}us/frame"
    GB.Sdl.close
  else
    IO.println "[bench] present: skipped (no SDL)"
