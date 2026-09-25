/-
  LeanAGB.Apu — GBA sound: DMG-compatible PSG (CH1/2 pulse, CH3 wave,
  CH4 noise) + DMA FIFO channels A/B + stereo mixer.

  Channel math reuses the proven DMG models (`LeanGameboy.Apu`) in the
  T-cycle domain (1 T = 4 GBA cycles): identical circuits, identical
  frequencies (131072/(2048-f) tone, 2097152/(2048-n) wave digits), so
  every DMG period/envelope/length/sweep tick transfers verbatim.
  Samples emit every 512 GBA cycles (128 T) — exactly 32768 Hz, so the
  audio clock is locked to the emulator with no resampling drift.

  Timer overflows pop one FIFO byte each and run the GBATEK refill
  procedure (16 bytes via DMA when ≤ 16 remain); the mixer mutes when
  SOUNDCNT_X bit 7 is clear, but FIFO/DMA mechanics stay live (they
  live in the timer/DMA domain, keeping voice positions exact across
  mute toggles). `advance` steps APU time before timers/PPU, so samples
  of a batch mix pre-batch FIFO state while endpoint pops apply after
  (exact except for measure-zero pop/sample coincidences).
-/
import LeanGameboy.Apu
import LeanAGB.Basic

namespace AGB

open GB

/-- GBA cycles per 32768 Hz sample (2^24 / 2^15). -/
def apuSamplePeriod : Nat := 512
/-- T-cycles per sample (512 / 4). -/
def apuSamplePeriodT : Nat := 128
/-- Frame-sequencer grid in T-cycles (512 Hz). -/
def apuSeqPeriodT : Nat := 8192

/-- UInt16 bit test. -/
def ubit (v : UInt16) (b : Nat) : Bool := ((v.toNat >>> b) &&& 1) == 1

/-- 32-byte Direct Sound FIFO (8×32-bit, signed bytes, LSB first).
    `out` is the sample-and-hold output (unchanged on empty pops). -/
structure AgbFifo where
  data : Array UInt8 := #[]
  out : Int := 0
deriving DecidableEq, Repr

def fifoSize (f : AgbFifo) : Nat := f.data.size

/-- Push (dropped when full — HW ignores overflow). -/
def fifoPush (f : AgbFifo) (v : UInt8) : AgbFifo :=
  if f.data.size < 32 then { f with data := f.data.push v } else f

/-- Signed value of a FIFO byte (-128..127). -/
def fifoSigned (v : UInt8) : Int :=
  if v.toNat >= 128 then (v.toNat : Int) - 256 else v.toNat

/-- Pop one byte to the sample-and-hold output (holds when empty). -/
def fifoPop (f : AgbFifo) : AgbFifo :=
  match f.data[0]? with
  | none => f
  | some b => { data := f.data.extract 1 f.data.size, out := fifoSigned b }

/-- Clear (FIFO reset bits). -/
def fifoClear (f : AgbFifo) : AgbFifo := { f with data := #[] }

/-- Full GBA APU state. PSG channels embed the proven DMG models
    (stepped in the T domain); `cycDebt`/`phaseDebt` conserve
    sub-sample time exactly (phases are unobservable except via `mix`,
    so they flush at sample points and register writes). -/
structure AgbApu where
  ch1 : PulseCh := {}
  ch2 : PulseCh := {}
  ch3 : WaveCh := {}
  ch4 : NoiseCh := {}
  waveRam : Array UInt8 := Array.replicate 32 0
  waveBank : Nat := 0
  waveDim : Bool := false
  waveForce : Bool := false
  fifoA : AgbFifo := {}
  fifoB : AgbFifo := {}
  cntL : UInt16 := 0
  cntH : UInt16 := 0
  cntX : UInt16 := 0
  bias : UInt16 := 0
  seqStep : Nat := 0
  seqT : Nat := 8192
  cycDebt : Nat := 0
  phaseDebt : Nat := 0
  sampleAcc : Nat := 0
  hpLX : Int := 0
  hpLY : Int := 0
  hpRX : Int := 0
  hpRY : Int := 0
  /-- 4th-order low-pass memory, two DF1 biquads per side:
      `[x1, x2, y1, y2]` then the second stage. -/
  lpL : Array Int := Array.replicate 8 0
  lpR : Array Int := Array.replicate 8 0
  out : ByteArray := ByteArray.empty
  /-- Fine-grid scratch voices (one Int per sample per side; drained
      through the decimator when `sampleRes ≠ 0`, else unused). -/
  foutL : Array Int := #[]
  foutR : Array Int := #[]
  /-- FIR decimator history per channel per cascade stage (3 stages
      cover res 1..3; zero-padded when short). -/
  firL : Array (Array Int) := #[#[], #[], #[]]
  firR : Array (Array Int) := #[#[], #[], #[]]

/-- Master enable (SOUNDCNT_X bit 7). -/
def apuMaster (a : AgbApu) : Bool := ubit a.cntX 7

/-- Mirror the playing 16-byte wave bank into the DMG channel window
    (length ticks and register storage still use the DMG struct). -/
def syncWaveBank (a : AgbApu) : AgbApu :=
  let base := (a.waveBank % 2) * 16
  let win := Array.mk ((List.range 16).map (fun i => a.waveRam.getD (base + i) 0))
  { a with ch3 := { a.ch3 with wave := win } }

/-- Wave digit at position `pos` (nibble, MSB-first per byte). Dim = 0
    loops 32 digits on the selected bank; dim = 1 loops 64 starting at
    the selected bank and continuing into the other (GBATEK wave page). -/
def waveDigit (a : AgbApu) (pos : Nat) : Nat :=
  let sel := a.waveBank % 2
  let (bank, q) :=
    if a.waveDim then
      let p := pos % 64
      (if p < 32 then sel else 1 - sel, p % 32)
    else (sel, pos % 32)
  let byte := (a.waveRam.getD (bank * 16 + q / 2) 0).toNat
  if q % 2 == 0 then byte / 16 else byte % 16

/-- Wave digit period in T-cycles (2097152/(2048-f) digits/sec). -/
def wavePeriodT (freq : Nat) : Nat := (2048 - freq % 2048) * 2

/-- Advance the wave position by `t` T-cycles (bulk, O(1)); the DMG
    struct carries timer/length/dac while `pos` runs 0..63 for the
    two-bank dimension (the DMG advance only models 0..31). -/
def waveAdvance (a : AgbApu) (t : Nat) : AgbApu :=
  if !a.ch3.enable || t == 0 then a
  else
    let p := wavePeriodT a.ch3.freq
    let timer0 := if a.ch3.timer == 0 then p else a.ch3.timer
    let clicks := (p - timer0) + t
    let steps := clicks / p
    let rem := clicks % p
    let timer' := if rem == 0 then p else p - rem
    { a with ch3 := { a.ch3 with timer := timer', pos := (a.ch3.pos + steps) % 64 } }

/-- Wave output 0..15 (DMG volume codes + GBA force-75% bit). -/
def waveOutput (a : AgbApu) : Nat :=
  if !a.ch3.enable || !a.ch3.dac then 0
  else
    let nib := waveDigit a a.ch3.pos
    if a.waveForce then nib * 3 / 4
    else match a.ch3.volCode with
      | 0 => 0 | 1 => nib | 2 => nib / 2 | _ => nib / 4

/-- Single LFSR clock (matches one `GB.noiseStepLoop` firing). -/
def noiseClock (lfsr : Nat) (width : Bool) : Nat :=
  let bit := ((lfsr % 2) ^^^ ((lfsr / 2) % 2)) % 2
  let l := (lfsr / 2) ||| (bit * 0x4000)
  (if width then (l &&& 0xFFBF) ||| (bit * 0x40) else l) % 0x8000

/-- Apply `k` LFSR clocks. -/
def noiseClocks : Nat → Nat → Bool → Nat
  | 0, lfsr, _ => lfsr
  | k + 1, lfsr, width => noiseClocks k (noiseClock lfsr width) width

/-- Bulk noise advance (O(clocks), not O(t)): identical result to
    `GB.NoiseCh.advance` (same clicks/steps/timer math as the pulse
    stepper), but the LFSR loop runs once per actual clock (usually
    0-1 per sample) instead of once per T-cycle. -/
def noiseAdvance (c : GB.NoiseCh) (t : Nat) : GB.NoiseCh :=
  if !c.enable then c
  else
    let p := GB.NoiseCh.noisePeriod c
    let timer0 := if c.timer == 0 then p else c.timer
    let clicks := (p - timer0) + t
    let steps := clicks / p
    let rem := clicks % p
    let timer' := if rem == 0 then p else p - rem
    { c with timer := timer', lfsr := noiseClocks steps c.lfsr c.width }

/-- Trigger a pulse channel (CH1/CH2 shared logic; mirrors the proven
    DMG `pulseTrigger`: enable follows DAC, length/envelope reload,
    CH1 reseeds the sweep shadow). -/
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

/-- One 512 Hz frame-sequencer tick (DMG step order: length on even
    steps, sweep on 2/6, envelope on 7). -/
def apuSeqTick (a : AgbApu) : AgbApu :=
  let st := a.seqStep % 8
  let a1 :=
    if st % 2 == 0 then
      { a with ch1 := PulseCh.lenTick a.ch1, ch2 := PulseCh.lenTick a.ch2,
               ch3 := WaveCh.lenTick a.ch3, ch4 := NoiseCh.lenTick a.ch4 }
    else a
  let a2 :=
    if st == 2 || st == 6 then
      { a1 with ch1 := PulseCh.sweepTick a1.ch1 } else a1
  let a3 :=
    if st == 7 then
      { a2 with
        ch1 := PulseCh.envTick a2.ch1
        ch2 := PulseCh.envTick a2.ch2
        ch4 := NoiseCh.envTick a2.ch4 } else a2
  { a3 with seqStep := a.seqStep + 1 }

/-- Apply `n` sequencer ticks. -/
def seqTickN : AgbApu → Nat → AgbApu
  | a, 0 => a
  | a, n + 1 => seqTickN (apuSeqTick a) n

/-- FIFO stereo contribution (raw signed units; volume 50/100%). -/
def fifoMix (a : AgbApu) : Int × Int :=
  let one (f : AgbFifo) (volBit rBit lBit : Nat) : Int × Int :=
    let vN : Int := if ((a.cntH.toNat >>> volBit) &&& 1) == 1 then 2 else 1
    let c := f.out * vN
    ((if ((a.cntH.toNat >>> lBit) &&& 1) == 1 then c else 0),
     (if ((a.cntH.toNat >>> rBit) &&& 1) == 1 then c else 0))
  let (l1, r1) := one a.fifoA 2 8 9
  let (l2, r2) := one a.fifoB 3 12 13
  (l1 + l2, r1 + r2)

/-- Stereo mix (s16 each): per-voice centered PSG contributions plus
    the FIFO contribution. Each voice adds `(output − 8)` only when
    routed, enabled, and DAC-on; anything else adds exactly 0 — an
    unrouted/idle sum must NOT carry a phantom bias (it would pop
    through the DC blocker on every routing/volume step). Scaled by
    the SOUNDCNT_H ratio (25/50/100%) and SOUNDCNT_L side volumes.
    Silent (master off) mixes true zero. -/
def apuMix (a : AgbApu) : Int × Int :=
  if !apuMaster a then (0, 0)
  else
    let o1 := PulseCh.output a.ch1
    let o2 := PulseCh.output a.ch2
    let o3 := waveOutput a
    let o4 := NoiseCh.output a.ch4
    -- GBATEK SOUNDCNT_L: bits 8-11 enable RIGHT, 12-15 enable LEFT
    -- (volumes 0-2 RIGHT / 4-6 LEFT were already correct).
    let lOn : Nat → Bool := fun b => ((a.cntL.toNat >>> (12 + b)) &&& 1) == 1
    let rOn : Nat → Bool := fun b => ((a.cntL.toNat >>> (8 + b)) &&& 1) == 1
    let voice (o : Nat) (en dac route : Bool) : Int :=
      if en && dac && route then (o : Int) - 8 else 0
    let l := voice o1 a.ch1.enable a.ch1.dac (lOn 0)
      + voice o2 a.ch2.enable a.ch2.dac (lOn 1)
      + voice o3 a.ch3.enable a.ch3.dac (lOn 2)
      + voice o4 a.ch4.enable a.ch4.dac (lOn 3)
    let r := voice o1 a.ch1.enable a.ch1.dac (rOn 0)
      + voice o2 a.ch2.enable a.ch2.dac (rOn 1)
      + voice o3 a.ch3.enable a.ch3.dac (rOn 2)
      + voice o4 a.ch4.enable a.ch4.dac (rOn 3)
    let psgN : Int :=
      match a.cntH.toNat &&& 3 with
      | 0 => 1 | 1 => 2 | _ => 4
    let volL : Int := (((a.cntL.toNat >>> 4) &&& 7) + 1 : Nat)
    let volR : Int := ((a.cntL.toNat &&& 7) + 1 : Nat)
    let pl := l * psgN * volL / 32
    let pr := r * psgN * volR / 32
    let (fl, fr) := fifoMix a
    let mixL := pl * 512 + fl * 32
    let mixR := pr * 512 + fr * 32
    let cl := if mixL > 32767 then 32767 else if mixL < -32768 then -32768 else mixL
    let cr := if mixR > 32767 then 32767 else if mixR < -32768 then -32768 else mixR
    (cl, cr)

/-- Append one stereo s16LE sample to the output buffer. -/
def pushS16LE (b : ByteArray) (v : Int) : ByteArray :=
  let c := if v > 32767 then 32767 else if v < -32768 then -32768 else v
  let u := (c % 65536 + 65536) % 65536
  (b.push (w8 u.toNat)).push (w8 (u.toNat / 256))

/-- Advance all channel phases by `t` T-cycles (bulk each; noise
    steps only on LFSR clocks). -/
def advancePhases (a : AgbApu) (t : Nat) : AgbApu :=
  waveAdvance
    { a with
      ch1 := a.ch1.advance t
      ch2 := a.ch2.advance t
      ch4 := noiseAdvance a.ch4 t } t

/-- Apply pending phase time (register writes observe phase timing). -/
def apuFlush (a : AgbApu) : AgbApu :=
  if a.phaseDebt == 0 then a
  else { (advancePhases a a.phaseDebt) with phaseDebt := 0 }

/-- DC-blocker step, left side (DMG `hpStep` shape). -/
def apuHpL (a : AgbApu) (x : Int) : AgbApu × Int :=
  let y := x - a.hpLX + GB.ApuState.tdiv1024 (a.hpLY * 1023)
  ({ a with hpLX := x, hpLY := y }, y)

/-- DC-blocker step, right side. -/
def apuHpR (a : AgbApu) (x : Int) : AgbApu × Int :=
  let y := x - a.hpRX + GB.ApuState.tdiv1024 (a.hpRY * 1023)
  ({ a with hpRX := x, hpRY := y }, y)

/-- Fixed-point scale for the reconstruction biquads (Q14). -/
def lpScale : Int := 16384

/-- Round-to-nearest division, symmetric about zero. -/
def divRound (v s : Int) : Int :=
  if 0 ≤ v then (v + s / 2) / s else -(((-v) + s / 2) / s)

/-- One DF1 biquad step. `a1`/`a2` are the denominator coefficients
    (the recursive terms are subtracted). Returns `(y, x1, x2, y1, y2)`. -/
def biquadStep (b0 b1 b2 a1 a2 x x1 x2 y1 y2 : Int) : Int × Int × Int × Int × Int :=
  let acc := b0 * x + b1 * x1 + b2 * x2 - a1 * y1 - a2 * y2
  let y0 := divRound acc lpScale
  let y := if y0 > 32767 then 32767 else if y0 < -32768 then -32768 else y0
  (y, x, x1, y, y1)

/-- Reconstruction low-pass: 4th-order Butterworth at 7 kHz
    (32768 Hz). Flat through 4 kHz, about −36 dB at 12 kHz and
    below −60 dB from 14 kHz up, so the FIFO zero-order-hold image
    and the top square/noise harmonics do not reach the host
    resampler (the old one-pole, k=3/4, was only −4 dB at 16 kHz,
    which is the buzz). Coefficients are Q14. -/
def apuLpMem (mem : Array Int) (x : Int) : Array Int × Int :=
  let (y0, x1, x2, y1, y2) :=
    biquadStep 4616 9231 4616 (-5409) 7487
      x (mem.getD 0 0) (mem.getD 1 0) (mem.getD 2 0) (mem.getD 3 0)
  let (y, x3, x4, y3, y4) :=
    biquadStep 3335 6670 3335 (-3908) 864
      y0 (mem.getD 4 0) (mem.getD 5 0) (mem.getD 6 0) (mem.getD 7 0)
  -- `set!` keeps the 8-cell delay line (no per-sample allocation).
  let mem := (mem.set! 0 x1).set! 1 x2 |>.set! 2 y1 |>.set! 3 y2
  let mem := (mem.set! 4 x3).set! 5 x4 |>.set! 6 y3 |>.set! 7 y4
  (mem, y)

def apuLpL (a : AgbApu) (x : Int) : AgbApu × Int :=
  let (mem, y) := apuLpMem a.lpL x
  ({ a with lpL := mem }, y)

def apuLpR (a : AgbApu) (x : Int) : AgbApu × Int :=
  let (mem, y) := apuLpMem a.lpR x
  ({ a with lpR := mem }, y)

/-- Emit `k` samples (128 T apart), advancing phases progressively.
    Every sample passes the DC blocker (first-order high-pass, ÷1024
    ≈ 5 Hz at 32768 Hz — the mixer's idle bias would otherwise hold a
    permanent offset and turn bias steps into pops; same pattern as
    the proven DMG `hpStep`) and the 7 kHz reconstruction low-pass. -/
def emitK : AgbApu → Nat → AgbApu
  | a, 0 => a
  | a, k + 1 =>
    let a := advancePhases a apuSamplePeriodT
    let (l, r) := apuMix a
    let (a, l) := apuHpL a l
    let (a, r) := apuHpR a r
    let (a, l) := apuLpL a l
    let (a, r) := apuLpR a r
    emitK { a with out := pushS16LE (pushS16LE a.out l) r } k

/-- SOUNDBIAS amplitude-resolution field (GBATEK: 0 = 9bit/32.768kHz,
    1 = 8bit/65.536kHz, 2 = 7bit/131.072kHz, 3 = 6bit/262.144kHz).
    The hardware renders at 2^res times the base grid; we emit at the
    same fine grid and decimate back to 32768 Hz on drain. -/
def sampleRes (a : AgbApu) : Nat := (a.bias.toNat >>> 14) &&& 0x3

/-- Output sample period in T-cycles for the current resolution
    (128 T at res 0, halving per step). -/
def samplePeriodT (a : AgbApu) : Nat := apuSamplePeriodT >>> sampleRes a

/-- Emit `k` fine-grid samples (DC-blocked, undecimated) into the
    scratch voices. The reconstruction low-pass is intentionally left
    to the drain-time FIR decimator (which subsumes it). -/
def emitKFine : AgbApu → Nat → Nat → AgbApu
  | a, _, 0 => a
  | a, periodT, k + 1 =>
    let a := advancePhases a periodT
    let (l, r) := apuMix a
    let (a, l) := apuHpL a l
    let (a, r) := apuHpR a r
    emitKFine { a with foutL := a.foutL.push l, foutR := a.foutR.push r }
      periodT k

/-- Advance the APU T-clock by `t`, emitting samples on the
    resolution grid (sequencer ticks apply batch-upfront, DMG-proven
    shape). At res 0 this is byte-for-byte the old path. -/
@[inline] def apuStepT (a : AgbApu) (t : Nat) : AgbApu :=
  if !apuMaster a || t == 0 then a
  else
    let seq0 := if a.seqT == 0 then apuSeqPeriodT else a.seqT
    let (seqT', ticks) :=
      if t < seq0 then (seq0 - t, 0)
      else
        let rest := t - seq0
        let rem := rest % apuSeqPeriodT
        (if rem == 0 then apuSeqPeriodT else apuSeqPeriodT - rem,
          1 + rest / apuSeqPeriodT)
    let a := seqTickN a ticks
    let per := samplePeriodT a
    let total := a.sampleAcc + t
    if sampleRes a == 0 then
      let a := emitK a (total / apuSamplePeriodT)
      { a with seqT := seqT', sampleAcc := total % apuSamplePeriodT }
    else
      let a := emitKFine a per (total / per)
      { a with seqT := seqT', sampleAcc := total % per }

/-- Advance the APU by `n` GBA cycles (T-domain via exact /4 debt). -/
@[inline] def apuStepCycles (a : AgbApu) (n : Nat) : AgbApu :=
  if !apuMaster a then a
  else
    let total := a.cycDebt + n
    let a := apuStepT { a with cycDebt := 0 } (total / 4)
    { a with cycDebt := total % 4 }

/-- Halfband decimator coefficients (31-tap, exact integers summing to
    2^15; only odd offsets from center are nonzero):
    `y[m] = (Σ h[k]·x[2m-k]) >> 15`. Passband flat to 0.2, -39 dB by
    0.3, -55 dB beyond (verified offline against mGBA's rolloff). -/
def hbCoeffs : Array Int :=
  #[16412, 10342, -3176, 1609, -878, 462, -221, 96, -56]

/-- One halfband decimate-by-2 stage over an Int voice with carried
    tail history. The buffer is padded to even length (duplicate last
    sample) so output positions stay globally even across drains —
    otherwise odd-length buffers would slip phase by one sample per
    drain (a 60 Hz micro-click). -/
def decim2 (hist xs : Array Int) : Array Int × Array Int :=
  let buf0 := hist ++ xs
  let buf := if buf0.size % 2 == 1 then buf0.push (buf0.getD (buf0.size - 1) 0) else buf0
  let n := buf.size
  let tailsz : Nat := 30
  let hist' :=
    if n <= tailsz then buf
    else buf.extract (n - tailsz) n
  -- outputs at even positions with a full 31-window on each side
  let outs := (List.range ((n + 14) / 2)).foldl (fun (acc : Array Int) m =>
    let c := 2 * m
    if 15 <= c && c + 15 < n then
      let y := (List.range 9).foldl (fun (acc : Int) k =>
        if k == 0 then acc + hbCoeffs.getD 0 0 * buf.getD c 0
        else acc + hbCoeffs.getD k 0 *
          (buf.getD (c - (2 * k - 1)) 0 + buf.getD (c + (2 * k - 1)) 0)) 0
      acc.push (y / 32768)
    else acc) #[]
  (outs, hist')

/-- Decimate fine voices to the 32768 Hz output grid (`stages` cascade
    steps for res 1..3), threading per-stage history. -/
def decimCascade : Array (Array Int) → Array Int → Nat → Array Int × Array (Array Int)
  | hists, xs, 0 => (xs, hists)
  | hists, xs, s + 1 =>
    let (outs, h0) := decim2 (hists.getD 0 #[]) xs
    let (fin, hs) := decimCascade (hists.set! 0 h0) outs s
    (fin, hs)

/-- One output sample: reconstruction low-pass, then s16LE stereo. -/
def pushFiltered (a : AgbApu) (b : ByteArray) (l r : Int) : AgbApu × ByteArray :=
  let (a, l) := apuLpL a l
  let (a, r) := apuLpR a r
  (a, pushS16LE (pushS16LE b l) r)

/-- Drain emitted sample bytes (frontend consumes them). At res 0 the
    samples were already low-passed in `emitK`. At res ≠ 0 the fine
    voices decimate through the FIR, then the same 7 kHz low-pass
    runs on the 32768 Hz result — games (Kirby included) leave
    SOUNDBIAS at 65 kHz, so this is the path that actually plays. -/
def apuDrain (a : AgbApu) : AgbApu × ByteArray :=
  if sampleRes a == 0 then
    ({ a with out := ByteArray.emptyWithCapacity 4096 }, a.out)
  else
    let r := sampleRes a
    let (dl, hl) := decimCascade a.firL a.foutL r
    let (dr, hr) := decimCascade a.firR a.foutR r
    let n := Nat.min dl.size dr.size
    let (a, out) := (List.range n).foldl (fun (acc : AgbApu × ByteArray) i =>
      let (a, b) := acc
      pushFiltered a b (dl.getD i 0) (dr.getD i 0))
      (a, ByteArray.emptyWithCapacity (4 * n + 16))
    ({ a with out := out, foutL := Array.emptyWithCapacity 1200, foutR := Array.emptyWithCapacity 1200, firL := hl, firR := hr }, out)

/-- Banked wave-RAM read (CPU sees the non-playing bank). -/
def apuWaveRead (a : AgbApu) (off : Nat) : UInt8 :=
  a.waveRam.getD (((1 - a.waveBank % 2) * 16 + off) % 32) 0

/-- Banked wave-RAM write (CPU sees the non-playing bank). -/
def apuWaveWrite (a : AgbApu) (off : Nat) (v : UInt8) : AgbApu :=
  { a with waveRam := a.waveRam.set! (((1 - a.waveBank % 2) * 16 + off) % 32) v }

/-- SOUNDCNT_X live status: master + per-channel active flags
    (bits 4-6 read 1, DMG NR52 convention). -/
def apuStatus (a : AgbApu) : UInt16 :=
  (if apuMaster a then (0x80 : UInt16) else 0)
    ||| (if a.ch1.enable then 1 else 0)
    ||| (if a.ch2.enable then 2 else 0)
    ||| (if a.ch3.enable then 4 else 0)
    ||| (if a.ch4.enable then 8 else 0)
    ||| 0x70

/-- Handle a 16-bit write to a sound lane (shadow already updated by
    the caller; phases flush first so triggers/frequency observe exact
    timing). Unlike DMG power-off, writes apply while muted (no GBATEK
    basis for ignoring them; only the mixer mutes). -/
def apuWrite16 (a : AgbApu) (lane : Nat) (v : UInt16) : AgbApu :=
  let a := apuFlush a
  let n := v.toNat
  match lane with
  | 0x04000060 =>
    { a with ch1 := { a.ch1 with
        sweepPeriod := (n / 16) % 8
        sweepDir := (n / 8) % 2 == 1
        sweepShift := n % 8 } }
  | 0x04000062 =>
    { a with ch1 := { a.ch1 with
        duty := (n / 64) % 4
        len := 64 - n % 64
        initVol := (n / 4096) % 16
        envDir := (n / 2048) % 2 == 1
        envPeriod := (n / 256) % 8
        dac := ((n / 256) &&& 0xF8) != 0 } }
  | 0x04000064 =>
    { a with ch1 :=
        let c := { a.ch1 with
          freq := n % 2048
          lenEnable := ((n / 16384) % 2) == 1 }
        if ((n / 32768) % 2) == 1 then pulseTrigger c true else c }
  | 0x04000068 =>
    { a with ch2 := { a.ch2 with
        duty := (n / 64) % 4
        len := 64 - n % 64
        initVol := (n / 4096) % 16
        envDir := (n / 2048) % 2 == 1
        envPeriod := (n / 256) % 8
        dac := ((n / 256) &&& 0xF8) != 0 } }
  | 0x0400006C =>
    { a with ch2 :=
        let c := { a.ch2 with
          freq := n % 2048
          lenEnable := ((n / 16384) % 2) == 1 }
        if ((n / 32768) % 2) == 1 then pulseTrigger c false else c }
  | 0x04000070 =>
    let a := { a with
      waveBank := (n / 64) % 2
      waveDim := ((n / 32) % 2) == 1
      ch3 := { a.ch3 with dac := ((n / 128) % 2) == 1 } }
    syncWaveBank a
  | 0x04000072 =>
    let ch3 := { a.ch3 with len := 256 - n % 256, volCode := (n / 8192) % 4 }
    { a with ch3 := ch3, waveForce := ((n / 32768) % 2) == 1 }
  | 0x04000074 =>
    { a with ch3 :=
        let c := { a.ch3 with
          freq := n % 2048
          lenEnable := ((n / 16384) % 2) == 1 }
        if ((n / 32768) % 2) == 1 then
          let c2 := { c with enable := c.dac, pos := 0 }
          if c2.len == 0 then { c2 with len := 256 } else c2
        else c }
  | 0x04000078 =>
    { a with ch4 := { a.ch4 with
        len := 64 - n % 64
        initVol := (n / 4096) % 16
        envDir := (n / 2048) % 2 == 1
        envPeriod := (n / 256) % 8
        dac := ((n / 256) &&& 0xF8) != 0 } }
  | 0x0400007C =>
    let lo := n % 256
    { a with ch4 :=
        let c := { a.ch4 with
          shift := (lo / 16) % 16
          width := (lo / 8) % 2 == 1
          divisor := lo % 8
          lenEnable := ((n / 16384) % 2) == 1 }
        if ((n / 32768) % 2) == 1 then
          let c2 := { c with
            enable := c.dac
            lfsr := 0x7FFF
            vol := c.initVol
            envTimer := c.envPeriod }
          if c2.len == 0 then { c2 with len := 64 } else c2
        else c }
  | 0x04000080 => { a with cntL := v }
  | 0x04000082 =>
    let a := { a with cntH := v }
    let a := if ubit v 11 then { a with fifoA := fifoClear a.fifoA } else a
    if ubit v 15 then { a with fifoB := fifoClear a.fifoB } else a
  | 0x04000084 => { a with cntX := v }
  | 0x04000088 =>
    -- On resolution change, drop fine-grid debt/history (avoids a
    -- transient; reconfig happens during silent init in practice).
    let e : Array (Array Int) := #[#[], #[], #[]]
    if ((a.bias.toNat >>> 14) &&& 0x3) == ((v.toNat >>> 14) &&& 0x3) then
      { a with bias := v }
    else
      { a with bias := v, sampleAcc := 0, foutL := #[], foutR := #[], firL := e, firR := e }
  | _ => a

end AGB
