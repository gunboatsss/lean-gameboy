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

end AGB
