/-
  LeanGameboy.Apu — DMG sound (CH1 pulse+sweep, CH2 pulse, CH3 wave,
  CH4 noise) + 512 Hz frame sequencer.

  Phase counters are advanced in bulk by elapsed T-cycles, so mixing
  stays exact without per-cycle stepping. Output is mono `Int`
  samples in Int16 range, accumulated in `samples`.
-/
import LeanGameboy.Basic

namespace GB

/-- Square-wave duty patterns (row = duty code, col = phase 0..7). -/
def dutyPat : Nat → Nat → Nat :=
  fun d i =>
    match d % 4, i % 8 with
    | 0, 0 => 0 | 0, 1 => 0 | 0, 2 => 0 | 0, 3 => 0
    | 0, 4 => 0 | 0, 5 => 0 | 0, 6 => 0 | 0, 7 => 1
    | 1, 0 => 1 | 1, 1 => 0 | 1, 2 => 0 | 1, 3 => 0
    | 1, 4 => 0 | 1, 5 => 0 | 1, 6 => 0 | 1, 7 => 1
    | 2, 0 => 1 | 2, 1 => 0 | 2, 2 => 0 | 2, 3 => 0
    | 2, 4 => 0 | 2, 5 => 1 | 2, 6 => 1 | 2, 7 => 1
    | _, 0 => 0 | _, 1 => 1 | _, 2 => 1 | _, 3 => 1
    | _, 4 => 1 | _, 5 => 1 | _, 6 => 1 | _, _ => 0

/-- Pulse channel (CH1/CH2). -/
structure PulseCh where
  enable : Bool := false
  dac : Bool := false
  -- frequency / phase
  freq : Nat := 0        -- 11-bit
  timer : Nat := 0       -- counts down T-cycles
  phase : Nat := 0
  duty : Nat := 0
  -- length
  len : Nat := 0
  lenEnable : Bool := false
  -- envelope
  vol : Nat := 0
  initVol : Nat := 0
  envDir : Bool := false
  envPeriod : Nat := 0
  envTimer : Nat := 0
  -- sweep (CH1 only)
  sweepPeriod : Nat := 0
  sweepDir : Bool := false  -- false = add, true = sub
  sweepShift : Nat := 0
  sweepTimer : Nat := 0
  sweepEnable : Bool := false
  shadow : Nat := 0
deriving Repr

/-- Wave channel (CH3). -/
structure WaveCh where
  enable : Bool := false
  dac : Bool := false
  freq : Nat := 0
  timer : Nat := 0
  pos : Nat := 0         -- 0..31 nibble position
  len : Nat := 0
  lenEnable : Bool := false
  volCode : Nat := 0
  wave : Array UInt8 := Array.mk (List.replicate 16 0)
deriving Repr

/-- Noise channel (CH4). -/
structure NoiseCh where
  enable : Bool := false
  dac : Bool := false
  lfsr : Nat := 0x7FFF
  timer : Nat := 0
  divisor : Nat := 0
  width : Bool := false  -- true = 7-bit mode
  shift : Nat := 0
  len : Nat := 0
  lenEnable : Bool := false
  vol : Nat := 0
  initVol : Nat := 0
  envDir : Bool := false
  envPeriod : Nat := 0
  envTimer : Nat := 0
deriving Repr

/-- Whole APU state. `phaseDebt` accumulates T-cycles of channel-phase
    time not yet applied: phases are unobservable except through `mix`,
    so stepping only advances timers and flushes phases at sample
    points (or on register writes — see `flush`).
    `sampleErr` is the Bresenham remainder that makes the 44100 Hz
    sample clock exact (see `nextSampleGap`); `hpX`/`hpY` are the
    DC-blocker (high-pass) filter state, so the mixer's constant bias
    decays to true silence instead of holding the speaker cone off
    centre. -/
structure ApuState where
  ch1 : PulseCh := {}
  ch2 : PulseCh := {}
  ch3 : WaveCh := {}
  ch4 : NoiseCh := {}
  nr50 : UInt8 := 0
  nr51 : UInt8 := 0
  nr52 : UInt8 := 0
  powered : Bool := false
  seqStep : Nat := 0
  seqTimer : Nat := 0     -- T-cycles until next 512 Hz tick (8192)
  sampleDebt : Nat := 0   -- T-cycles until next 44100 Hz sample (95/96)
  sampleErr : Nat := 0    -- Bresenham remainder, always < 44100
  phaseDebt : Nat := 0    -- unapplied channel-phase T-cycles
  hpX : Int := 0          -- DC-blocker previous raw input
  hpY : Int := 0          -- DC-blocker previous filtered output
  -- Emitted samples as S16LE bytes (unboxed: avoids GC marking costs
  -- that boxed `Array Int` would incur as the buffer grows headless).
  samples : ByteArray := ByteArray.empty

namespace PulseCh

/-- Period in T-cycles for the current frequency. -/
def period (c : PulseCh) : Nat := (2048 - c.freq % 2048) * 4

/-- Advance phase by `t` T-cycles in O(1) (no per-cycle loop). -/
def advance (c : PulseCh) (t : Nat) : PulseCh :=
  if !c.enable || t == 0 then c
  else
    let p := period c
    let timer0 := if c.timer == 0 then p else c.timer
    -- clicks until (and including) the next phase step, then full periods
    let clicks := (p - timer0) + t
    let steps := clicks / p
    let rem := clicks % p
    let timer' := if rem == 0 then p else p - rem
    { c with timer := timer', phase := (c.phase + steps) % 8 }

/-- Current DAC output 0..15. -/
def output (c : PulseCh) : Nat :=
  if !c.enable || !c.dac then 0
  else (dutyPat c.duty c.phase) * c.vol

/-- Envelope tick (frame sequencer step 7). -/
def envTick (c : PulseCh) : PulseCh :=
  if c.envPeriod == 0 then c
  else
    let t := if c.envTimer == 0 then c.envPeriod else c.envTimer - 1
    if t == 0 then
      let v := if c.envDir then c.vol + 1 else c.vol - 1
      if v > 15 || (c.vol == 0 && !c.envDir) then { c with envTimer := c.envPeriod }
      else { c with vol := v, envTimer := c.envPeriod }
    else { c with envTimer := t }

/-- Length tick (sequencer steps 0/2/4/6). -/
def lenTick (c : PulseCh) : PulseCh :=
  if !c.lenEnable then c
  else if c.len == 0 then c
  else
    let l := c.len - 1
    if l == 0 then { c with len := l, enable := false } else { c with len := l }

/-- Sweep tick (sequencer steps 2/6), CH1 only. -/
def sweepTick (c : PulseCh) : PulseCh :=
  if !c.sweepEnable || c.sweepPeriod == 0 then c
  else
    let t := if c.sweepTimer == 0 then c.sweepPeriod else c.sweepTimer - 1
    if t != 0 then { c with sweepTimer := t }
    else
      let delta := c.shadow / (2 ^ c.sweepShift)
      let f := if c.sweepDir then c.shadow - delta else c.shadow + delta
      if f > 2047 then { c with enable := false, sweepTimer := c.sweepPeriod }
      else if c.sweepShift == 0 then { c with sweepTimer := c.sweepPeriod }
      else { c with freq := f, shadow := f, sweepTimer := c.sweepPeriod }

end PulseCh

namespace WaveCh

def period (c : WaveCh) : Nat := (2048 - c.freq % 2048) * 2

def advance (c : WaveCh) (t : Nat) : WaveCh :=
  if !c.enable || t == 0 then c
  else
    let p := period c
    let timer0 := if c.timer == 0 then p else c.timer
    let clicks := (p - timer0) + t
    let steps := clicks / p
    let rem := clicks % p
    let timer' := if rem == 0 then p else p - rem
    { c with timer := timer', pos := (c.pos + steps) % 32 }

def output (c : WaveCh) : Nat :=
  if !c.enable || !c.dac then 0
  else
    let byte := if c.pos / 2 < c.wave.size then c.wave[c.pos / 2]! else 0
    let nib := if c.pos % 2 == 0 then (byte.toNat / 16) else (byte.toNat % 16)
    match c.volCode with
    | 0 => 0 | 1 => nib | 2 => nib / 2 | _ => nib / 4

def lenTick (c : WaveCh) : WaveCh :=
  if !c.lenEnable then c
  else if c.len == 0 then c
  else
    let l := c.len - 1
    if l == 0 then { c with len := l, enable := false } else { c with len := l }

end WaveCh

namespace NoiseCh

def noisePeriod (c : NoiseCh) : Nat :=
  let div : Nat :=
    match c.divisor with
    | 0 => 8 | 1 => 16 | 2 => 32 | 3 => 48 | 4 => 64 | 5 => 80 | 6 => 96 | _ => 112
  div * (1 <<< c.shift)

/-- LFSR stepping loop, hoisted to top level for induction:
    `period`/`width` used to be captured from `c` (identical body). -/
def noiseStepLoop (period : Nat) (width : Bool) : Nat → Nat → Nat → Nat × Nat
  | 0, timer, lfsr => (timer, lfsr)
  | k + 1, timer, lfsr =>
    if timer <= 1 then
      let bit := ((lfsr % 2) ^^^ ((lfsr / 2) % 2)) % 2
      let l := (lfsr / 2) ||| (bit * 0x4000)
      let l' := if width then (l &&& 0xFFBF) ||| (bit * 0x40) else l
      noiseStepLoop period width k period (l' % 0x8000)
    else noiseStepLoop period width k (timer - 1) lfsr

def advance (c : NoiseCh) (t : Nat) : NoiseCh :=
  if !c.enable then c
  else
    let p := noisePeriod c
    let (timer', lfsr') :=
      noiseStepLoop p c.width t (if c.timer == 0 then p else c.timer) c.lfsr
    { c with timer := timer', lfsr := lfsr' }

def output (c : NoiseCh) : Nat :=
  if !c.enable || !c.dac then 0
  else if c.lfsr % 2 == 1 then 0 else c.vol

def envTick (c : NoiseCh) : NoiseCh :=
  if c.envPeriod == 0 then c
  else
    let t := if c.envTimer == 0 then c.envPeriod else c.envTimer - 1
    if t == 0 then
      if c.envDir then
        if c.vol >= 15 then { c with envTimer := c.envPeriod }
        else { c with vol := c.vol + 1, envTimer := c.envPeriod }
      else
        if c.vol == 0 then { c with envTimer := c.envPeriod }
        else { c with vol := c.vol - 1, envTimer := c.envPeriod }
    else { c with envTimer := t }

def lenTick (c : NoiseCh) : NoiseCh :=
  if !c.lenEnable then c
  else if c.len == 0 then c
  else
    let l := c.len - 1
    if l == 0 then { c with len := l, enable := false } else { c with len := l }

end NoiseCh

namespace ApuState

/-- Mix one sample (-32768..32767). -/
def mix (s : ApuState) : Int :=
  if !s.powered then 0
  else
    let o1 := PulseCh.output s.ch1
    let o2 := PulseCh.output s.ch2
    let o3 := WaveCh.output s.ch3
    let o4 := NoiseCh.output s.ch4
    let lOn : Nat → Bool := fun b => bitGet s.nr51 b
    let rOn : Nat → Bool := fun b => bitGet s.nr51 (b + 4)
    let sel : Nat → Nat := fun o => o
    let l := (if lOn 0 then sel o1 else 0) + (if lOn 1 then sel o2 else 0) +
             (if lOn 2 then sel o3 else 0) + (if lOn 3 then sel o4 else 0)
    let r := (if rOn 0 then sel o1 else 0) + (if rOn 1 then sel o2 else 0) +
             (if rOn 2 then sel o3 else 0) + (if rOn 3 then sel o4 else 0)
    let volL := (s.nr50.toNat / 16) % 8
    let volR := s.nr50.toNat % 8
    -- each channel 0..15, centre at 7.5; scale to Int16
    let dl : Int := (l : Int) - 30
    let dr : Int := (r : Int) - 30
    let m : Int := (dl * (volL + 1) + dr * (volR + 1)) * 64
    if m > 32767 then 32767 else if m < -32768 then -32768 else m

/-- One 512 Hz frame-sequencer tick. -/
def seqTick (s : ApuState) : ApuState :=
  let st := s.seqStep % 8
  let s1 :=
    if st % 2 == 0 then
      { s with ch1 := PulseCh.lenTick s.ch1, ch2 := PulseCh.lenTick s.ch2,
               ch3 := WaveCh.lenTick s.ch3, ch4 := NoiseCh.lenTick s.ch4 }
    else s
  let s2 :=
    if st == 2 || st == 6 then
      { s1 with ch1 := PulseCh.sweepTick s1.ch1 } else s1
  let s3 :=
    if st == 7 then
      { s2 with
        ch1 := PulseCh.envTick s2.ch1
        ch2 := PulseCh.envTick s2.ch2
        ch4 := NoiseCh.envTick s2.ch4 } else s2
  { s3 with seqStep := s.seqStep + 1 }

/-- True when no channel can currently produce sound *and* no muted
    state (length countdowns, sweep) can affect a future trigger.
    Envelope-only drift is safe to skip: triggers reload volume. -/
def allQuiet (s : ApuState) : Bool :=
  !s.ch1.enable && !s.ch2.enable && !s.ch3.enable && !s.ch4.enable &&
  !(s.ch1.lenEnable && s.ch1.len != 0) &&
  !(s.ch2.lenEnable && s.ch2.len != 0) &&
  !(s.ch3.lenEnable && s.ch3.len != 0) &&
  !(s.ch4.lenEnable && s.ch4.len != 0) &&
  !s.ch1.sweepEnable

/-- Silence level of `mix` when all channels are off (DC offset from
    master volume/panning). This is the *raw* mixer bias fed into the
    DC blocker — the emitted level decays to 0 (see `hpStep`), keeping
    the audio clock exact without a permanent DC offset. -/
def silence (s : ApuState) : Int :=
  let volL := (s.nr50.toNat / 16) % 8
  let volR := s.nr50.toNat % 8
  let m : Int := (-30 * (volL + 1) + -30 * (volR + 1)) * 64
  if m > 32767 then 32767 else if m < -32768 then -32768 else m

/-- Base T-cycles per 44100 Hz sample (4194304 / 44100 ≈ 95.109). -/
def sampleBase : Nat := 95

/-- Bresenham step: 4194304 - 95 * 44100 = 4804. -/
def sampleErrStep : Nat := 4804

/-- Bresenham modulus (audio rate). -/
def sampleErrMax : Nat := 44100

/-- Schedule the next sample gap from the Bresenham error: most gaps
    are 95 T-cycles, every ~9th is 96, so the mean gap is exactly
    4194304 / 44100 T-cycles. A fixed 95-cycle gap would run ~0.1%
    fast, slowly filling SDL's queue until whole frames get dropped
    (audible pops); a fixed 96 would starve it instead. -/
def nextSampleGap (err : Nat) : Nat × Nat :=
  let e := err + sampleErrStep
  if e >= sampleErrMax then (96, e - sampleErrMax) else (95, e)

/-- Truncated division by 1024 (toward zero). Lean's `/` on `Int`
    floors, which would make every value in `(-1024, 0]` a fixed point
    of the DC blocker below (frozen residual DC); truncation leaves 0
    as the only fixed point. -/
def tdiv1024 (v : Int) : Int :=
  if 0 <= v then v / 1024 else -((-v) / 1024)

/-- One DC-blocker (first-order high-pass) step:
    `y = x - hpX + trunc(hpY * 1023 / 1024)` (≈ 7 Hz cutoff at 44.1 kHz).
    Removes the mixer's constant bias and turns abrupt register-write
    steps into quickly-decaying thumps, like the Game Boy's output
    capacitor. -/
def hpStep (s : ApuState) (x : Int) : ApuState × Int :=
  let y := x - s.hpX + tdiv1024 (s.hpY * 1023)
  ({ s with hpX := x, hpY := y }, y)

/-- Advance all channel phases by `t` T-cycles (bulk, O(1) each
    except noise which iterates its short LFSR period). -/
def advanceCh (s : ApuState) (t : Nat) : ApuState :=
  { s with
    ch1 := s.ch1.advance t
    ch2 := s.ch2.advance t
    ch3 := s.ch3.advance t
    ch4 := s.ch4.advance t }

/-- Apply all pending phase time to the channels. Called before any
    register write that could observe or change phase timing
    (period/frequency writes and triggers), keeping samples exact. -/
def flush (s : ApuState) : ApuState :=
  if s.phaseDebt == 0 then s
  else
    let st := s.advanceCh s.phaseDebt
    { st with phaseDebt := 0 }

/-- Apply `n` frame-sequencer ticks. -/
def seqTicks : ApuState → Nat → ApuState
  | s, 0 => s
  | s, n + 1 => seqTicks s.seqTick n

/-- Append one S16LE sample to the buffer. -/
def pushSample (b : ByteArray) (v : Int) : ByteArray :=
  let c := if v > 32767 then 32767 else if v < -32768 then -32768 else v
  let u := (c % 65536 + 65536) % 65536
  (b.push (w8 u.toNat)).push (w8 (u.toNat / 256))

/-- Advance the APU by `dots` T-cycles, emitting exact-~44.1 kHz samples
    (mean gap exactly 4194304 / 44100 T-cycles via `nextSampleGap`).
    Channel phases are applied lazily: most batches only advance
    timers and accumulate `phaseDebt`; phases flush progressively at
    sample points (and fully on register writes via `flush`), which is
    exact since phases are unobservable except through `mix`.
    Every emitted sample goes through the DC blocker (`hpStep`), so
    silent stretches emit true zero instead of the mixer's DC bias. -/
def stepDots (s : ApuState) (dots : Nat) : ApuState :=
  if !s.powered then s
  else
    let t := dots
    -- sequencer timers (length/envelope/sweep need no phases)
    let seq0 := if s.seqTimer == 0 then 8192 else s.seqTimer
    let (seqTimer', ticks) :=
      if t < seq0 then (seq0 - t, 0)
      else
        let rest := t - seq0
        let rem := rest % 8192
        (if rem == 0 then 8192 else 8192 - rem, 1 + rest / 8192)
    -- time until the first sample of this batch, plus the already-
    -- scheduled Bresenham error (`sampleDebt == 0` only in fresh state)
    let (debt0, err0) : Nat × Nat :=
      if s.sampleDebt == 0 then (sampleBase, s.sampleErr + sampleErrStep)
      else (s.sampleDebt, s.sampleErr)
    if allQuiet s && ticks == 0 then
      -- silent fast path (phases frozen; flushed on register writes)
      if debt0 > t then
        { s with
          seqTimer := seqTimer'
          sampleDebt := debt0 - t
          sampleErr := err0
          phaseDebt := s.phaseDebt + t }
      else
        let (stA, y0) := hpStep s (silence s)
        let stB := { stA with seqTimer := seqTimer' }
        let st0 := { stB with samples := pushSample stB.samples y0 }
        let (g1, er1) := nextSampleGap err0
        let rec fill : Nat → Nat → Nat → Nat → ApuState → ApuState
          | 0, _, _, _, st => st
          | f + 1, rem, gap, err, st =>
            if gap > rem then
              { st with
                sampleDebt := gap - rem
                sampleErr := err
                phaseDebt := st.phaseDebt + t }
            else
              let (st1, y) := hpStep st (silence s)
              let st2 := { st1 with samples := pushSample st1.samples y }
              let (g, er) := nextSampleGap err
              fill f (rem - gap) g er st2
        fill (t + 1) (t - debt0) g1 er1 st0
    else
      let s1 := seqTicks s ticks
      let s1 := { s1 with seqTimer := seqTimer' }
      if debt0 > t then
        -- no samples this batch: accumulate debt, no channel work
        { s1 with
          phaseDebt := s1.phaseDebt + t
          sampleDebt := debt0 - t
          sampleErr := err0 }
      else
        -- flush pending + batch time progressively at sample points
        let st0 := s1.advanceCh (s1.phaseDebt + debt0)
        let (st0b, y0) := hpStep st0 st0.mix
        let st0c := { st0b with
          phaseDebt := 0
          samples := pushSample st0b.samples y0 }
        let (g1, er1) := nextSampleGap err0
        let rec loop : Nat → Nat → Nat → Nat → ApuState → ApuState
          | 0, _, _, _, st => st
          | f + 1, rem, gap, err, st =>
            if gap > rem then
              let st1 := st.advanceCh rem
              { st1 with phaseDebt := 0, sampleDebt := gap - rem, sampleErr := err }
            else
              let st1 := st.advanceCh gap
              let (st2, y) := hpStep st1 st1.mix
              let st3 := { st2 with samples := pushSample st2.samples y }
              let (g, er) := nextSampleGap err
              loop f (rem - gap) g er st3
        loop (t + 1) (t - debt0) g1 er1 st0c

/-- Advance the APU by `mCycles` M-cycles at single speed
    (1 M-cycle = 4 T-cycles). Double-speed callers use `stepDots`
    with 2 T-cycles per M-cycle instead. -/
def step (s : ApuState) (mCycles : Nat) : ApuState :=
  s.stepDots (mCycles * 4)

/-- Drain accumulated sample bytes (frontend consumes them). -/
def drain (s : ApuState) : ApuState × ByteArray :=
  ({ s with samples := ByteArray.empty }, s.samples)

end ApuState

end GB
