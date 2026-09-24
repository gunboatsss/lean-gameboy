/-
  agb-synth — listening-ladder synthesizer (reproducible test tones).

  Usage: agb-synth [outdir]   (default `/tmp`)
  Writes the diagnostic WAV set (48kHz stereo s16LE) mirroring the
  throwaway python ladder 1:1: deterministic LCG noise (seed 7/11),
  the GB 15-bit LFSR (`AGB.noiseClock` itself), envelopes, sweeps,
  a dense mini-mix, and a smooth-vs-sample-held arpeggio pair.
  Float ops lower to C doubles, so output matches the python
  references bit-for-bit (modulo libm versions).
-/
import LeanAGB

open AGB

def synthSR : Nat := 48000

/-- Little-endian s16 push with clamping. -/
def pushS16C (b : ByteArray) (v : Int) : ByteArray :=
  let c := if v > 32767 then 32767 else if v < -32768 then -32768 else v
  let u := (c % 65536 + 65536) % 65536
  (b.push (w8 u.toNat)).push (w8 (u.toNat / 256))

/-- WAV writer (stereo s16LE @synthSR). -/
def writeWavFile (path : System.FilePath) (data : ByteArray) : IO Unit := do
  let ascii (s : String) : Array UInt8 :=
    s.toList.toArray.map (fun c => w8 c.toNat)
  let h := ByteArray.mk (ascii "RIFF")
  let h := pushU32LE h (36 + data.size).toUInt32
  let h := h ++ ByteArray.mk (ascii "WAVEfmt ")
  let h := pushU32LE h 16
  let h := pushU16LE h 1
  let h := pushU16LE h 2
  let h := pushU32LE h synthSR.toUInt32
  let h := pushU32LE h (synthSR * 4).toUInt32
  let h := pushU16LE h 4
  let h := pushU16LE h 16
  let h := h ++ ByteArray.mk (ascii "data")
  let h := pushU32LE h data.size.toUInt32
  IO.FS.writeBinFile path (h ++ data)

/-- Float in [-1, 1] to s16 (clamped, C-cast truncation). -/
def f2s16 (x : Float) (peak : Nat) : Int :=
  let scaled := (max (-1.0) (min 1.0 x)) * peak.toFloat
  if scaled >= 0.0 then (scaled.toUInt32.toNat : Int)
  else -((-scaled).toUInt32.toNat : Int)

/-- Render `secs` seconds of mono `f` (index → Float in [-1, 1]) at
    `peak` s16 amplitude, duplicated to stereo. -/
def render (secs : Nat) (peak : Nat) (f : Nat → Float) : ByteArray :=
  (List.range (secs * synthSR)).foldl (fun b i =>
    let v := f2s16 (f i) peak
    pushS16C (pushS16C b v) v) ByteArray.empty

/-- LCG step (deterministic white noise; glibc constants). -/
def lcgNext (s : Nat) : Nat := (1103515245 * s + 12345) % 2147483648

def lcgVal (s : Nat) : Float := (s.toFloat / 1073741824.0) - 1.0

def sq (f : Float) (i : Nat) : Float :=
  if Float.sin (2.0 * 3.14159265358979 * f * i.toFloat / synthSR.toFloat) >= 0.0
  then 1.0 else -1.0

def main (args : List String) : IO Unit := do
  let out := if args.length > 0 then args[0]! else "/tmp"
  let w (name : String) (d : ByteArray) : IO Unit := do
    writeWavFile (out ++ "/" ++ name) d
    IO.println s!"[synth] {name} ({d.size}B)"
  w "t_sine440.wav" (render 4 10000 (fun i =>
    Float.sin (2.0 * 3.14159265358979 * 440.0 * i.toFloat / synthSR.toFloat)))
  w "t_square440.wav" (render 4 10000 (sq 440.0))
  w "t_beat.wav" (render 4 8000 (fun i =>
    0.5 * sq 440.0 i + 0.5 * sq 445.0 i))
  w "t_gate.wav" (render 4 8000 (fun i =>
    if ((i / (synthSR / 10)) % 2) == 0 then sq 440.0 i else 0.0))
  -- white-noise bursts (LCG seed 7, gated 8Hz)
  let nz := (List.range (4 * synthSR)).foldl
    (fun (acc : Array Float × Nat) _ =>
      let s := lcgNext acc.2
      (acc.1.push (lcgVal s), s)) (#[], 7)
  w "t_nzgate.wav" (render 4 8000 (fun i =>
    if ((i / (synthSR / 8)) % 2) == 0 then nz.1.getD i 0.0 else 0.0))
  -- GB 15-bit LFSR bursts (the engine's own LFSR, clocked per 8 samples)
  let lfsrSeq := (List.range (4 * synthSR)).foldl
    (fun (acc : Array Float × Nat) i =>
      let prev := acc.2
      let cur := if i % 8 == 0 then noiseClock prev false else prev
      (acc.1.push (if cur % 2 == 0 then 1.0 else -1.0), cur))
    (#[], 0x7FFF)
  w "t_lfsr.wav" (render 4 8000 (fun i =>
    if ((i / (synthSR / 6)) % 2) == 0 then lfsrSeq.1.getD i 0.0 else 0.0))
  -- exponential decay retriggered 2Hz
  w "t_decay.wav" (render 5 8000 (fun i =>
    let t := (i % (synthSR / 2)).toFloat / (synthSR / 2).toFloat
    sq 440.0 i * Float.exp (-3.0 * t)))
  -- phase-continuous 220->880 sweep repeating 2Hz
  w "t_sweep.wav" (render 5 8000 (fun i =>
    let t := (i % (synthSR / 2)).toFloat / (synthSR / 2).toFloat
    let phi := (220.0 * (synthSR / 2).toFloat / Float.log 4.0)
      * (Float.exp (Float.log 4.0 * t) - 1.0) / synthSR.toFloat
    if Float.sin (2.0 * 3.14159265358979 * phi) >= 0.0 then 1.0 else -1.0))
  -- dense mini-chiptune
  w "t_dense.wav" (render 5 8000 (fun i =>
    let t := i.toFloat / synthSR.toFloat
    let g := Float.exp (-1.5 * (t - (i / synthSR).toFloat))
    0.3 * sq 220.0 i + 0.25 * sq 277.0 i + 0.2 * sq 330.0 i
      + 0.25 * nz.1.getD (i % nz.1.size) 0.0))
  -- smooth arpeggio vs 15.765kHz sample-and-hold (FIFO mechanism proxy)
  let arpNotes : Array (Float × Float × Float) :=
    #[(220.0, 0.0, 0.5), (277.18, 0.5, 0.5), (329.63, 1.0, 0.5),
      (440.0, 1.5, 0.5), (329.63, 2.0, 0.5), (277.18, 2.5, 0.5),
      (220.0, 3.0, 0.5), (196.0, 3.5, 0.5), (164.81, 4.0, 0.5),
      (146.83, 4.5, 0.5)]
  let arp (i : Nat) : Float :=
    let t := i.toFloat / synthSR.toFloat
    arpNotes.foldl (fun (acc : Float) (e : Float × Float × Float) =>
      match e with
      | (f, t0, dur) =>
        if t0 <= t && t < t0 + dur then
          let tt := t - t0
          acc + 0.25 * Float.sin (2.0 * 3.14159265358979 * f * t)
            * Float.exp (-2.0 * tt / dur)
            + 0.075 * Float.sin (2.0 * 2.0 * 3.14159265358979 * f * t)
            * Float.exp (-2.0 * tt / dur)
        else acc) 0.0
  w "t_smooth.wav" (render 5 8000 arp)
  let per : Float := synthSR.toFloat / (16777216.0 / 1064.0)
  let hold (i : Nat) : Float :=
    arp (((i.toFloat / per).toUInt32.toNat.toFloat * per).toUInt32.toNat)
  w "t_zoh.wav" (render 5 8000 hold)
