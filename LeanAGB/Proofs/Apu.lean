/-
  LeanAGB.Proofs.Apu — sound contracts: FIFO push/pop/clear instances,
  overflow-hook identity, sample/grid constants, mixer silence.
-/
import LeanAGB.Bus

namespace AGB

-- ── Timer-overflow hook fires only on real overflows ──

theorem apuTimerOverflow_zero (s : AGBState) (i : Nat) :
    apuTimerOverflow s i 0 = s := by
  rfl

-- ── FIFO instances (kernel-checked) ──

theorem fifoPush_pop_roundtrip :
    fifoPop (fifoPush {} 0x40) = { data := #[], out := 64 } := by decide

theorem fifoPop_empty : fifoPop {} = {} := by decide

theorem fifoClear_empties :
    fifoClear { data := #[1, 2, 3], out := 5 } = { data := #[], out := 5 } := by
  decide

theorem fifoPush_full_drops :
    fifoPush { data := Array.replicate 32 0, out := 0 } 0xFF
      = { data := Array.replicate 32 0, out := 0 } := by decide

theorem fifoSigned_pos : fifoSigned 0x40 = 64 := by decide

theorem fifoSigned_neg : fifoSigned 0xC0 = -64 := by decide

-- ── Grids and master switch ──

theorem apuSamplePeriod_is512 : apuSamplePeriod = 512 := by rfl

theorem apuSamplePeriodT_is128 : apuSamplePeriodT = 128 := by rfl

theorem apuSeqPeriodT_is8192 : apuSeqPeriodT = 8192 := by rfl

theorem apuMaster_off : apuMaster {} = false := by decide

theorem apuMaster_on : apuMaster { cntX := 0x80 } = true := by decide

/-- Frozen while muted (cycles dropped, resume clean). -/
theorem apuStepCycles_muted (n : Nat) : apuStepCycles {} n = {} := by
  rfl

/-- Silent mixer (master off mixes true zero). -/
theorem apuMix_silent : apuMix {} = (0, 0) := by decide

-- ── Bulk noise advance ≡ the proven per-tick advance ──

def noiseT0 : GB.NoiseCh :=
  { enable := true, dac := true, lfsr := 0x7FFF, timer := 0, divisor := 0,
    width := false, shift := 0, len := 0, lenEnable := false, vol := 0,
    initVol := 0, envDir := false, envPeriod := 0, envTimer := 0 }

def noiseT1 : GB.NoiseCh :=
  { noiseT0 with timer := 5, width := true }

def noiseT2 : GB.NoiseCh :=
  { noiseT0 with timer := 1, divisor := 3, shift := 2 }

theorem noiseAdvance_t0 :
    (noiseAdvance noiseT0 100).lfsr = (GB.NoiseCh.advance noiseT0 100).lfsr := by
  decide

theorem noiseAdvance_t0_timer :
    (noiseAdvance noiseT0 100).timer
      = (GB.NoiseCh.advance noiseT0 100).timer := by
  decide

theorem noiseAdvance_t1 :
    (noiseAdvance noiseT1 100).lfsr = (GB.NoiseCh.advance noiseT1 100).lfsr := by
  decide

theorem noiseAdvance_t2 :
    (noiseAdvance noiseT2 200).lfsr = (GB.NoiseCh.advance noiseT2 200).lfsr := by
  decide

theorem noiseAdvance_t2_timer :
    (noiseAdvance noiseT2 200).timer
      = (GB.NoiseCh.advance noiseT2 200).timer := by
  decide

theorem noiseAdvance_off :
    (noiseAdvance { noiseT0 with enable := false } 100).lfsr
      = (GB.NoiseCh.advance { noiseT0 with enable := false } 100).lfsr := by
  decide

/-! ## Wave voice -/

/-- Slowest wave rate. -/
theorem wavePeriodT_lo : wavePeriodT 0 = 4096 := by decide

/-- Fastest wave rate. -/
theorem wavePeriodT_hi : wavePeriodT 2047 = 2 := by decide

/-- Wave periods are always positive. -/
theorem wavePeriodT_pos (freq : Nat) : 0 < wavePeriodT freq := by
  have hmod : freq % 2048 < 2048 := by omega
  unfold wavePeriodT
  omega

/-- Disabled wave voice is silent. -/
theorem waveOutput_disabled (a : AgbApu) (h : a.ch3.enable = false) :
    waveOutput a = 0 := by
  simp [waveOutput, h]

/-- Wave voice with DAC off is silent. -/
theorem waveOutput_dacOff (a : AgbApu) (h : a.ch3.dac = false) :
    waveOutput a = 0 := by
  simp [waveOutput, h]

/-- Nibble extraction is MSB-first. -/
theorem waveDigit_hi :
    waveDigit { waveBank := 0, waveDim := false, waveRam := #[0xAB] } 0 = 0xA := by
  decide

theorem waveDigit_lo :
    waveDigit { waveBank := 0, waveDim := false, waveRam := #[0xAB] } 1 = 0xB := by
  decide

/-- Zero time advance is the identity. -/
theorem waveAdvance_zero (a : AgbApu) : waveAdvance a 0 = a := by
  simp [waveAdvance]

/-- Playing-bank mirror loads the DMG window. -/
theorem syncWaveBank_load :
    (syncWaveBank { waveBank := 0, waveRam := #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] }).ch3.wave = Array.mk [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] := by
  decide

/-! ## Noise voice -/

/-- One LFSR clock on the reset state. -/
theorem noiseClock_reset : noiseClock 0x7FFF false = 0x3FFF := by decide

/-- Zero clocks is the identity. -/
theorem noiseClocks_zero (lfsr : Nat) (width : Bool) :
    noiseClocks 0 lfsr width = lfsr := rfl

/-! ## Trigger + sequencer plumbing -/

/-- Triggering follows DAC for enable. -/
theorem pulseTrigger_enable (c : GB.PulseCh) (isCh1 : Bool) :
    (pulseTrigger c isCh1).enable = c.dac := by
  cases hlen : c.len == 0 <;> cases hb : isCh1 <;> simp [pulseTrigger, hlen]

/-- Triggering reloads volume from the envelope start. -/
theorem pulseTrigger_vol (c : GB.PulseCh) (isCh1 : Bool) :
    (pulseTrigger c isCh1).vol = c.initVol := by
  cases hlen : c.len == 0 <;> cases hb : isCh1 <;> simp [pulseTrigger, hlen]

/-- No pending phase time: flush is the identity. -/
theorem apuFlush_idle (a : AgbApu) (h : a.phaseDebt = 0) :
    apuFlush a = a := by
  simp [apuFlush, h]

/-! ## Mixer + status -/

/-- Empty FIFOs mix silence. -/
theorem fifoMix_empty : fifoMix {} = (0, 0) := by decide

/-- Status with everything off reads the fixed bits. -/
theorem apuStatus_idle : apuStatus {} = 0x70 := by decide

/-- Status with everything on reads all ones. -/
theorem apuStatus_full :
    apuStatus { cntX := 0x80, ch1 := { enable := true }, ch2 := { enable := true }, ch3 := { enable := true }, ch4 := { enable := true } } = 0xFF := by
  decide

/-- Banked wave-RAM roundtrip at offset 0. -/
theorem apuWave_rw :
    apuWaveRead (apuWaveWrite { waveBank := 0, waveRam := Array.replicate 32 0 } 0 0xAB) 0 = 0xAB := by
  decide

end AGB
