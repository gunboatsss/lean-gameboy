/-
  agb-bench — GBA microbenchmarks + interleaved A/B pairs.

  Usage: agb-bench ROM.gba [--frames N] [--rounds R] [--warmup W] [--only a,b,c]
  Workloads: frame (end-to-end emu), stepcpu, advance, dma (bulk-vs-slow pair),
             render, memo (memo-hit). Machine-parseable `[agb-bench]` lines;
  `state:` / `fbcheck:` lines pin cross-build determinism.
-/
import LeanAGB

open AGB
open AGB.Sdl

structure ABenchOpts where
  rom : String := ""
  frames : Nat := 10
  rounds : Nat := 5
  warmup : Nat := 8
  only : String := "all"

def parseABenchArgs : List String → ABenchOpts → ABenchOpts
  | [], o => o
  | "--frames" :: n :: rest, o => parseABenchArgs rest { o with frames := n.toNat! }
  | "--rounds" :: n :: rest, o => parseABenchArgs rest { o with rounds := n.toNat! }
  | "--warmup" :: n :: rest, o => parseABenchArgs rest { o with warmup := n.toNat! }
  | "--only" :: l :: rest, o => parseABenchArgs rest { o with only := l }
  | a :: rest, o =>
    if o.rom == "" && !a.startsWith "--" then parseABenchArgs rest { o with rom := a }
    else parseABenchArgs rest o

def inOnly (o : ABenchOpts) (name : String) : Bool :=
  o.only == "all" || (o.only.splitToList (· == ',')).contains name

/-- Time `iters` applications of `f`, threading state. The `cycles`
    checksum is folded inside the window so the whole computation is
    forced before `t1` (no dead-code/thunk leakage out of the window). -/
def timeIters (f : AGBState → AGBState) (s : AGBState) (iters : Nat) :
    IO (AGBState × Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let rec loop : AGBState → Nat → Nat → AGBState × Nat
    | s, 0, c => (s, c)
    | s, k + 1, c => let s2 := f s; loop s2 k (c + s2.cycles % 1000000007)
  let (s2, chk) := loop s iters 0
  let t1 ← IO.monoNanosNow
  pure (s2, chk, t1 - t0)

def medianF (a : Array Float) : Float :=
  if a.size == 0 then 0 else (a.qsort (· < ·)).getD (a.size / 2) 0

/-- 16KB EWRAM pattern at 0x02000000 (bulk source; idempotent target). -/
def fillEwram16k (s : AGBState) : AGBState :=
  let pat : ByteArray :=
    (List.range 16384).foldl (fun b i => b.push (w8 (i % 251))) ByteArray.empty
  { s with ewram := pat ++ s.ewram.extract 16384 s.ewram.size }

/-- Bulk arm: the `dmaRun` dispatch (fires `dmaBulk` here). -/
def dmaBulkF (s : AGBState) : AGBState :=
  dmaRun s 0x02000000 0x02010000 0x1000 true 4 4 4

/-- Slow arm: the legacy word-by-word loop, identical semantics. -/
def dmaSlowF (s : AGBState) : AGBState :=
  dmaCopy s 0x02000000 0x02010000 0x1000 true 4 4

/-- Interleaved pair: alternate A/B start order per round to cancel drift.
    Returns (final state, ns/iter A, ns/iter B, median per-round B/A). -/
def benchPair (fA fB : AGBState → AGBState) (s : AGBState)
    (itersA itersB rounds : Nat) : IO (AGBState × Nat × Nat × Float) := do
  let mut s := s
  let mut tA := 0
  let mut tB := 0
  let mut ratios : Array Float := #[]
  for r in List.range rounds do
    if r % 2 == 0 then
      let (s1, _, dtA) ← timeIters fA s itersA; s := s1
      let (s2, _, dtB) ← timeIters fB s itersB; s := s2
      tA := tA + dtA; tB := tB + dtB
      ratios := ratios.push (dtB.toFloat * itersA.toFloat / (dtA.toFloat * itersB.toFloat))
    else
      let (s1, _, dtB) ← timeIters fB s itersB; s := s1
      let (s2, _, dtA) ← timeIters fA s itersA; s := s2
      tA := tA + dtA; tB := tB + dtB
      ratios := ratios.push (dtB.toFloat * itersA.toFloat / (dtA.toFloat * itersB.toFloat))
  pure (s, tA / (itersA * rounds), tB / (itersB * rounds), medianF ratios)

def fbCheck (s : AGBState) : Nat :=
  s.fb.foldl (fun acc c => acc + c.toNat) 0

/-- Bare single-field commit: the struct-copy floor. -/
def commit1F : AGBState → AGBState := fun st => { st with cycles := st.cycles + 1 }

/-- Five-field commit: the fused-advance commit shape. -/
def commit5F : AGBState → AGBState := fun st =>
  let a := st.apu
  let t := st.timers
  let q := st.irq
  let p := { st.ppu with dots := st.ppu.dots }
  let c := st.cycles
  { st with apu := a, timers := t, irq := q, ppu := p, cycles := c + 1 }

/-- HLE CpuSet state: 16KB EWRAM→EWRAM 32-bit copy via r0/r1/r2. -/
def cpusetState (s : AGBState) : AGBState :=
  let r := fillEwram16k s
  let regs := ((r.regs.set 0 0x02000000).set 1 0x02010000).set 2 0x04001000
  { r with regs := regs }

def printState (s : AGBState) : IO Unit := do
  IO.println s!"[agb-bench] state: cycles={s.cycles} pc={s.regs.pc.toNat} frame={s.ppu.frame} if={s.irq.if_.toNat} apu={s.apu.out.size} bias={s.apu.bias.toNat} res={sampleRes s.apu} fout={s.apu.foutL.size}"

def main (args : List String) : IO Unit := do
  let o := parseABenchArgs args {}
  if o.rom == "" then
    IO.println "usage: agb-bench ROM.gba [--frames N] [--rounds R] [--warmup W] [--only frame,stepcpu,advance,dma,render,memo]"
  else do
    let bytes ← IO.FS.readBinFile o.rom
    let s0 := AGBState.freshAuto bytes (detectSaveKind bytes)
    IO.println s!"[agb-bench] rom={bytes.size} warmup={o.warmup} frames={o.frames} rounds={o.rounds}"
    let s := runFrames s0 o.warmup
    let mut s := s
    if inOnly o "frame" then do
      -- One honest `timeIters` window per frame (a bare `s := runFrame s`
      -- in a `for` loop stores an unevaluated thunk and measures nothing;
      -- only values forced in a strict context cross honestly here).
      let mut tot := 0
      let mut mx := 0
      for _ in List.range (o.frames * o.rounds) do
        let (s2, _, dt) ← timeIters runFrame s 1
        s := s2
        tot := tot + dt
        mx := Nat.max mx dt
      IO.println s!"[agb-bench] frame: {tot}ns for {o.frames * o.rounds} frames ({tot / (o.frames * o.rounds)}ns/frame max={mx}ns)"
      printState s
    if inOnly o "stepcpu" then do
      let (s2, _, dt) ← timeIters stepCPU s 100000
      s := s2
      IO.println s!"[agb-bench] stepcpu: {dt}ns for 100000 iters ({dt / 100000}ns/iter)"
    if inOnly o "advance" then do
      let (s2, _, dt) ← timeIters (fun st => advance st 2) s 100000
      s := s2
      IO.println s!"[agb-bench] advance2: {dt}ns for 100000 iters ({dt / 100000}ns/iter)"
    if inOnly o "dma" then do
      let sd := fillEwram16k s
      let (_, aNs, bNs, med) ← benchPair dmaBulkF dmaSlowF sd 50 50 o.rounds
      IO.println s!"[agb-bench] pair dma16k: bulk={aNs}ns/iter slow={bNs}ns/iter speedup={med}x rounds={o.rounds}"
    if inOnly o "render" then do
      let t0 ← IO.monoNanosNow
      let mut chk := 0
      for _ in List.range (20 * o.rounds) do
        let s2 := renderFrame s
        s := s2; chk := chk + s2.fb.size % 1000000007
      let t1 ← IO.monoNanosNow
      IO.println s!"[agb-bench] render: {(t1 - t0)}ns for {20 * o.rounds} iters ({(t1 - t0) / (20 * o.rounds)}ns/iter chk={chk})"
      IO.println s!"[agb-bench] fbcheck: {fbCheck s}"
    if inOnly o "sprites" then do
      -- 96 overlapping 32×32 sprites (shape 0, size 2). Same pixels the
      -- scanline painter must cover when a scene is full of OBJs.
      let mut oam := s.oam
      for i in List.range 96 do
        let y := w16 (i * 3 % 200)
        let x := w16 (i * 5 % 240)
        let a1 := x ||| (w16 2 <<< 14)
        let a2 := w16 ((i * 8) % 512)
        oam := bset16LE oam (i * 8) y
        oam := bset16LE oam (i * 8 + 2) a1
        oam := bset16LE oam (i * 8 + 4) a2
      let sd := { s with oam := oam, ppu := { s.ppu with dispcnt := (s.ppu.dispcnt &&& 0xFF78) ||| 0x1000 } }
      let t0 ← IO.monoNanosNow
      let mut chk := 0
      let mut st := sd
      for _ in List.range (8 * o.rounds) do
        let s2 := renderFrame st
        st := s2; chk := chk + (s2.fb.getD 100 0).toNat
      let t1 ← IO.monoNanosNow
      IO.println s!"[agb-bench] sprites: {(t1 - t0)}ns for {8 * o.rounds} iters ({(t1 - t0) / (8 * o.rounds)}ns/iter chk={chk})"
    if inOnly o "memo" then do
      let t0 ← IO.monoNanosNow
      let mut m : RenderMemo := {}
      let mut n := 0
      for _ in List.range (20 * o.rounds) do
        let (s2, m2) := memoRenderFrame s m
        s := s2; m := m2; n := n + s2.fb.size % 1000000007
      let t1 ← IO.monoNanosNow
      IO.println s!"[agb-bench] memo-hit: {(t1 - t0)}ns for {20 * o.rounds} iters ({(t1 - t0) / (20 * o.rounds)}ns/iter chk={n})"
    if inOnly o "ms" then do
      -- render miss every iteration (one fresh vram byte per iter forces
      -- full render + snapshot; the set! copy stays outside the window)
      let mut m : RenderMemo := {}
      let mut tot := 0
      let mut n := 0
      for k in List.range (20 * o.rounds) do
        let sv := { s with vram := s.vram.set! (k % s.vram.size) (w8 k) }
        let t0 ← IO.monoNanosNow
        let (s2, m2) := memoRenderFrame sv m
        let t1 ← IO.monoNanosNow
        tot := tot + (t1 - t0)
        m := m2; n := n + s2.fb.size % 1000000007; s := s2
      IO.println s!"[agb-bench] memomiss: {tot}ns for {20 * o.rounds} ({tot / (20 * o.rounds)}ns/iter chk={n})"
    if inOnly o "apuroute" then do
      for f in List.range o.frames do
        let a := s.apu
        IO.println s!"[apuroute] f={s.ppu.frame} cntL={a.cntL.toNat} cntH={a.cntH.toNat} cntX={a.cntX.toNat} bias={a.bias.toNat} ch1={a.ch1.enable},{a.ch1.dac},{a.ch1.vol} ch2={a.ch2.enable},{a.ch2.dac},{a.ch2.vol} ch3={a.ch3.enable},{a.ch3.dac},{a.ch3.volCode} ch4={a.ch4.enable},{a.ch4.dac},{a.ch4.vol} fAout={a.fifoA.out} fBout={a.fifoB.out}"
        s := runFrame s
    if inOnly o "stems" then do
      -- per-voice stem levels at 8 points across one frame (struct tweaks
      -- on copies; no shipped-code changes): who makes the sound, when?
      let cyc0 := s.cycles
      for k in List.range 8 do
        let target := cyc0 + (k + 1) * AGB_CYCLES_PER_FRAME / 8
        while s.cycles < target do
          s := stepCPU s
        let a := s.apu
        let full := apuMix a
        let no1 := apuMix { a with ch1 := { a.ch1 with enable := false } }
        let no2 := apuMix { a with ch2 := { a.ch2 with enable := false } }
        let no4 := apuMix { a with ch4 := { a.ch4 with enable := false } }
        let noF := apuMix { a with fifoA := {}, fifoB := {} }
        IO.println s!"[stems] k={k} full={full} no1={no1} no2={no2} no4={no4} noF={noF} cntL={a.cntL.toNat}"
    if inOnly o "fifodump" then do
      for f in List.range 4 do
        let a := s.apu
        let d1 := s.dma.ch.getD 1 {}
        let d2 := s.dma.ch.getD 2 {}
        IO.println s!"[fifodump] f={s.ppu.frame} cntH={a.cntH.toNat} A={a.fifoA.data} B={a.fifoB.data}"
        IO.println s!"[fifodump] ch1 sad={d1.sad.toNat} dad={d1.dad.toNat} h={d1.cnt_h.toNat} ch2 sad={d2.sad.toNat} dad={d2.dad.toNat} h={d2.cnt_h.toNat}"
        IO.println s!"[fifodump] src16={List.range 16 |>.map (fun i => (memRead8 s (d1.sad + w32 i)).toNat)}"
        IO.println s!"[fifodump] srcB64={List.range 64 |>.map (fun i => (memRead8 s (d2.sad + w32 i)).toNat)}"
        let blk := List.range 4 |>.map (fun b =>
          (List.range 64).foldl (fun (acc : Int × Nat) i =>
            let v : Int := (memRead8 s (d2.sad + w32 (b * 64 + i))).toNat
            (acc.1 + v, Nat.max acc.2 (if i == 0 then 0 else 0))) (0, 0))
        IO.println s!"[fifodump] blkmeans={blk.map (fun p => p.1 / 64)}"
        s := runFrame s
    if inOnly o "aputrace" then do
      -- per-frame APU internals (voice enables, wave pos, noise lfsr,
      -- FIFO levels/sizes, timer0 state, emit bytes): watch the machinery
      for f in List.range o.frames do
        let a := s.apu
        let t0 := s.timers.ch.getD 0 {}
        IO.println s!"[aputrace] f={s.ppu.frame} e13={a.ch1.enable},{a.ch2.enable},{a.ch3.enable},{a.ch4.enable} wpos={a.ch3.pos} wtimer={a.ch3.timer} nlfsr={a.ch4.lfsr} ntimer={a.ch4.timer} fA={a.fifoA.out},{fifoSize a.fifoA} fB={a.fifoB.out},{fifoSize a.fifoB} t0={t0.cnt.toNat},{t0.reload.toNat},{t0.acc} out={a.out.size} master={apuMaster a} bias={a.bias.toNat} res={sampleRes a} fout={a.foutL.size}"
        IO.println s!"[aputrace] sweep1=({a.ch1.sweepPeriod},{a.ch1.sweepShift},{a.ch1.sweepEnable},{a.ch1.shadow}) f={a.ch1.freq},{a.ch2.freq} vol={a.ch1.vol},{a.ch2.vol},{a.ch4.vol} envT={a.ch1.envTimer},{a.ch2.envTimer},{a.ch4.envTimer} len={a.ch1.len},{a.ch2.len},{a.ch4.len} seq={a.seqStep}"
        s := runFrame s
    if inOnly o "pacing" then do
      -- Windowed-loop mirror (minus SDL): setButtons(0), runFrame,
      -- memoRenderFrame-or-skip, apuDrain into a virtual device pool
      -- (cap + trim exactly like the shim; 16KB HW buffer absorbs down
      -- to -16384 before an audible gap accrues). Detects systematic
      -- starvation/trim in OUR push/pacing logic.
      let mut m : RenderMemo := {}
      let mut skips := 0
      let mut due := 0
      let mut frac := 0
      let mut t0 ← IO.monoMsNow
      due := t0
      let mut lastT := t0
      let mut pool : Int := 0
      let mut gapMs := 0
      let mut worstEpisode := 0
      let mut curEpisode := 0
      let mut nskip := 0
      let mut trimB := 0
      let mut minPool : Int := 0
      let cap : Int := 32768 / 5 * 4
      let n := o.frames * o.rounds
      let mut idx := 0
      let mut alive := false
      for _ in List.range n do
        idx := idx + 1
        let s1 := setButtons s 0
        let s2 := runFrame s1
        s := s2
        let now ← IO.monoMsNow
        let dt : Int := (now : Int) - (lastT : Int)
        lastT := now
        pool := pool - dt * 131072 / 1000
        let skip := due < now && skips < 3
        if skip then
          nskip := nskip + 1
          skips := skips + 1
        else
          let (s3, m3) ← presentAgbFrame s m
          s := s3; m := m3; skips := 0
        let (apu, abuf) := apuDrain s.apu
        s := { s with apu := apu }
        if pool < cap && abuf.size > 0 then
          let room := cap - pool
          let mm := Nat.min abuf.size room.toNat / 4 * 4
          pool := pool + (mm : Int)
          trimB := trimB + (abuf.size - mm)
        if idx > 30 then
          if pool < 0 then
            if pool < -16384 then
              gapMs := gapMs + 1
              curEpisode := curEpisode + 1
            else
              curEpisode := 0
          else
            curEpisode := 0
          worstEpisode := Nat.max worstEpisode curEpisode
          minPool := if pool < minPool then pool else minPool
        let (due2, frac2) := nextDeadline due frac
        due := due2; frac := frac2
        -- Audio-clock pacing mirror (queue stands in for audioQueued;
        -- device assumed present once it ever reads nonzero).
        alive := alive || pool > 0
        let base := if due > now then due - now else 0
        let d :=
          if !alive then base
          else if pool < 6000 then 0
          else if pool > 20000 then base * 2
          else base
        -- Real pacing without SDL: busy-wait until the target time
        -- (delayMs is a no-op unless a window is open; burning CPU here
        -- only affects thermals, not the push/drain arithmetic).
        let rec snoozeTo : Nat → Nat → IO Unit
          | _, 0 => pure ()
          | tgt, n + 1 => do
            let t ← IO.monoMsNow
            if tgt > t then snoozeTo tgt n else pure ()
        if d != 0 then
          snoozeTo (now + d) 1000000
      -- NOTE: presentAgbFrame needs SDL; without a window its blit/present
      -- calls are no-ops, so this measures emu+render+memo pacing faithfully.
      IO.println s!"[agb-bench] pacing: iters={n} gapIters={gapMs} worstEpisode={worstEpisode} skips={nskip} trimB={trimB} minPool={minPool}"
    if inOnly o "present" then do
      let rc ← openWindow 2
      IO.println s!"[agb-bench] sdl open rc={rc}"
      if rc == 0 then
        let (sP, _) ← presentAgbFrame s {}
        let t0 ← IO.monoNanosNow
        for _ in List.range 60 do blit32 sP.fb
        let t1 ← IO.monoNanosNow
        IO.println s!"[agb-bench] blit32: {(t1 - t0)}ns for 60 ({(t1 - t0) / 60}ns/iter)"
        let t0 ← IO.monoNanosNow
        for _ in List.range 60 do present
        let t1 ← IO.monoNanosNow
        IO.println s!"[agb-bench] sdlpresent: {(t1 - t0)}ns for 60 ({(t1 - t0) / 60}ns/iter)"
        let (_, abuf) := apuDrain sP.apu
        let t0 ← IO.monoNanosNow
        for _ in List.range 60 do audioPush abuf
        let t1 ← IO.monoNanosNow
        IO.println s!"[agb-bench] audiopush: {(t1 - t0)}ns for 60 ({(t1 - t0) / 60}ns/iter bytes={abuf.size})"
        let t0 ← IO.monoNanosNow
        for _ in List.range (o.frames * o.rounds) do
          let s2 := runFrame s
          let (s3, _) ← presentAgbFrame s2 {}
          s := s3
        let t1 ← IO.monoNanosNow
        IO.println s!"[agb-bench] hostiter: {(t1 - t0)}ns for {o.frames * o.rounds} ({(t1 - t0) / (o.frames * o.rounds)}ns/iter)"
        close
    if inOnly o "parts" then do
      -- APU-off advance: fused-commit floor (timers disabled, master off)
      let sq : AGBState := { s with apu := {}, timers := {} }
      let (_, _, dt) ← timeIters (fun st => advance st 2) sq 100000
      IO.println s!"[agb-bench] adv-noapu: {dt}ns for 100000 iters ({dt / 100000}ns/iter)"
      -- live halt-jump advance on evolving gameplay state (the real cost?)
      let (_, _, dt) ← timeIters (fun st => advance st (haltJump st)) s 20000
      IO.println s!"[agb-bench] adv-livejump: {dt}ns for 20000 iters ({dt / 20000}ns/iter)"
      -- APU step alone on the live (audio-on) state
      let ap := s.apu
      let t0 ← IO.monoNanosNow
      let mut a := ap
      let mut c := 0
      for _ in List.range 100000 do
        a := apuStepCycles a 2; c := c + a.cycDebt
      let t1 ← IO.monoNanosNow
      IO.println s!"[agb-bench] apustep2: {(t1 - t0)}ns for 100000 iters ({(t1 - t0) / 100000}ns/iter chk={c})"
      -- execThumb alone on a fixed simple op (no fetch/advance)
      let ins := decodeThumb 0x1C01
      let t0 ← IO.monoNanosNow
      let mut e := s
      let mut c2 := 0
      for _ in List.range 100000 do
        let (e2, cc) := execThumb e ins; e := e2; c2 := c2 + cc
      let t1 ← IO.monoNanosNow
      IO.println s!"[agb-bench] execthumb: {(t1 - t0)}ns for 100000 iters ({(t1 - t0) / 100000}ns/iter chk={c2} pc={e.regs.pc.toNat})"
      -- decodeThumb alone
      let t0 ← IO.monoNanosNow
      let mut d := 0
      for k in List.range 200000 do
        d := d + match decodeThumb (k % 65536).toUInt16 with
          | .movsImm _ _ => 1 | _ => 2
      let t1 ← IO.monoNanosNow
      IO.println s!"[agb-bench] decode: {(t1 - t0)}ns for 200000 iters ({(t1 - t0) / 200000}ns/iter chk={d})"
      -- memRead32 over EWRAM
      let t0 ← IO.monoNanosNow
      let mut m2 := 0
      for k in List.range 200000 do
        m2 := m2 + (memRead32 s (0x02000000 + (k % 1024 * 4 : Nat).toUInt32)).toNat
      let t1 ← IO.monoNanosNow
      IO.println s!"[agb-bench] memread: {(t1 - t0)}ns for 200000 iters ({(t1 - t0) / 200000}ns/iter chk={m2})"
      -- pure instruction steps: infinite Thumb B-loop, no halts/IRQs
      let sl := loadROM (ByteArray.mk #[0xFE, 0xE7])
      let (sl2, _, dt) ← timeIters stepCPU sl 50000
      IO.println s!"[agb-bench] instrstep: {dt}ns for 50000 iters ({dt / 50000}ns/iter pc={sl2.regs.pc.toNat})"
      -- bare single-field commit: the struct-copy floor
      let ( _, _, dt) ← timeIters commit1F s 100000
      IO.println s!"[agb-bench] commit1: {dt}ns for 100000 iters ({dt / 100000}ns/iter)"
      -- fast-B tail alone on B-loop state (no stepCPU wrapper)
      let sl := loadROM (ByteArray.mk #[0xFE, 0xE7])
      let w0 := memRead32 sl 0x08000000
      let hw0 := fetchHw w0 0x08000000
      let t0 ← IO.monoNanosNow
      let mut fb := sl
      let mut cf := 0
      for _ in List.range 50000 do
        match stepThumbFast fb 0x08000000 w0 hw0 with
        | some f2 => fb := f2; cf := cf + f2.cycles
        | none => cf := cf + 1
      let t1 ← IO.monoNanosNow
      IO.println s!"[agb-bench] fastbtail: {(t1 - t0)}ns for 50000 ({(t1 - t0) / 50000}ns/iter chk={cf})"
      -- five-field commit: the fused-advance commit shape
      let (_, _, dt) ← timeIters commit5F s 100000
      IO.println s!"[agb-bench] commit5: {dt}ns for 100000 iters ({dt / 100000}ns/iter)"
      -- HLE CpuSet 16KB (decompression-path proxy; idempotent target)
      let sc := cpusetState s
      let (_, _, dt) ← timeIters hleSwiCpuSet sc 50
      IO.println s!"[agb-bench] hlecpuset: {dt}ns for 50 iters ({dt / 50}ns/iter)"
      -- dynamic Thumb opcode mix over live gameplay (pure fetch+classify)
      let mut fast := 0; let mut mem := 0; let mut oth := 0
      for _ in List.range 30000 do
        if !s.halted && !irqPending s.irq && cpsrT s.regs.cpsr then
          let pc := s.regs.pc
          let hw := fetchHw (memRead32 s (pc &&& 0xFFFFFFFC)) pc
          let v := hw.toNat
          let top := v >>> 11
          if top == 28 || top == 4 || top == 5 || top == 0 || top == 1
              || top == 3 || (v >>> 10) == 16 then
            fast := fast + 1
          else if top == 12 || top == 13 then
            mem := mem + 1
          else
            oth := oth + 1
        s := stepCPU s
      IO.println s!"[agb-bench] opmix: fast10={fast} memimm={mem} other={oth} pc={s.regs.pc.toNat}"
      -- dynamic step mix over live gameplay (projections force each step)
      let mut th := 0; let mut ar := 0; let mut ha := 0; let mut ir := 0
      for _ in List.range 50000 do
        if s.halted then ha := ha + 1
        else if irqPending s.irq then ir := ir + 1
        else if cpsrT s.regs.cpsr then th := th + 1
        else ar := ar + 1
        s := stepCPU s
      IO.println s!"[agb-bench] mix: thumb={th} arm={ar} halt={ha} irq={ir} pc={s.regs.pc.toNat}"
      -- timer/jump snapshot + jump-size histogram (what caps halt jumps?)
      for i in List.range 4 do
        let ch := s.timers.ch.getD i {}
        IO.println s!"[agb-bench] tmr{i}: ctrl={ch.ctrl.toNat} cnt={ch.cnt.toNat} reload={ch.reload.toNat} acc={ch.acc}"
      IO.println s!"[agb-bench] jump={haltJump s} dots={s.ppu.dots} master={apuMaster s.apu} fifoA={fifoSize s.apu.fifoA} fifoB={fifoSize s.apu.fifoB}"
      let mut hsmall := 0; let mut hmed := 0; let mut hbig := 0
      for _ in List.range 20000 do
        let j := haltJump s
        if j < 16 then hsmall := hsmall + 1
        else if j < 200 then hmed := hmed + 1
        else hbig := hbig + 1
        s := stepCPU s
      IO.println s!"[agb-bench] jumps: small={hsmall} med={hmed} big={hbig} pc={s.regs.pc.toNat} halted={s.halted}"
      -- IRQ/halt snapshot (why does Kirby park?)
      IO.println s!"[agb-bench] irq: ie={s.irq.ie.toNat} if={s.irq.if_.toNat} ime={s.irq.ime} halted={s.halted} wake={haltWake s} pend={irqPending s.irq}"
      -- per-frame composition over 5 frames, mirroring runFrame dispatch
      for f in List.range 5 do
        let target := s.cycles + AGB_CYCLES_PER_FRAME
        let mut nj := 0; let mut jc := 0; let mut nt := 0; let mut ni := 0
        let mut nw := 0; let mut nq := 0
        let mut cfa := 0; let mut cme := 0; let mut cot := 0
        let mut cpush := 0; let mut cstm := 0; let mut cbl := 0
        let mut clit := 0; let mut cbc := 0; let mut chi := 0; let mut cot2 := 0
        let mut out0 := s.apu.out.size
        while s.cycles < target do
          if s.halted then
            if haltWake s then nw := nw + 1
            else
              let j := haltJump s
              nj := nj + 1; jc := jc + j
            s := stepHaltJump s
          else if irqPending s.irq then
            nq := nq + 1
            s := stepCPU s
          else
            if cpsrT s.regs.cpsr then
              nt := nt + 1
              let pc := s.regs.pc
              let v := (fetchHw (memRead32 s (pc &&& 0xFFFFFFFC)) pc).toNat
              let top := v >>> 11
              if top == 28 || top == 4 || top == 5 || top == 0 || top == 1
                  || top == 3 || (v >>> 10) == 16 then
                cfa := cfa + 1
              else if top == 12 || top == 13 then
                cme := cme + 1
              else
                cot := cot + 1
                if top == 22 || top == 23 then cpush := cpush + 1
                else if top == 24 || top == 25 then cstm := cstm + 1
                else if top == 30 || top == 31 then cbl := cbl + 1
                else if top == 9 then clit := clit + 1
                else if (v >>> 12) == 13 then cbc := cbc + 1
                else if (v >>> 10) == 17 then chi := chi + 1
                else cot2 := cot2 + 1
            else ni := ni + 1
            s := stepCPU s
        let emit := s.apu.out.size - out0
        IO.println s!"[agb-bench] fstat{f}: jumps={nj} jumpcyc={jc} wake={nw} thumb={nt} arm={ni} irq={nq} emitB={emit} cyc={s.cycles} fast={cfa} mem={cme} oth={cot} pushpop={cpush} ldmstm={cstm} bl={cbl} lit={clit} bc={cbc} hi={chi} rest={cot2}"
