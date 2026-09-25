/-
  LeanGameboy.Proofs.Apu — channel phase-step frame properties.

  Stepping never alters channel configuration (only phase/timer
  positions), and zero-stepping is the identity. These pin the frame
  that the bulk O(1) phase math — and the phase-debt batching built
  on it — must preserve.

  NOTE: `NoiseCh.advance` stepping loops through its LFSR, so its
  bulk loop lives in `Apu.noiseStepLoop` (hoisted from a `let rec` for
  induction) with composition (`noiseStepLoop_add`), timer positivity,
  and channel additivity below.

  The second half pins the voice/mixer layer: duty tables, periods,
  DAC gating, length expiry, envelope hold, mixer silence, and the
  sample-clock constants. -/
import LeanGameboy.Apu

namespace GB

/-- Zero-stepping is the identity (pulse). -/
theorem pulse_advance_zero (c : PulseCh) : c.advance 0 = c := by
  simp [PulseCh.advance]

/-- Zero-stepping is the identity (wave). -/
theorem wave_advance_zero (c : WaveCh) : c.advance 0 = c := by
  simp [WaveCh.advance]

/-- Phase advance is additive (pulse): two bulk steps equal one
    combined step. Guards discharge by casing `enable` and zero steps
    (via `pulse_advance_zero`); the counting core is `Nat.add_mul_div_left`
    with `omega` for the `mod 8` phase and timer bookkeeping. -/
theorem pulse_advance_additive (c : PulseCh) (a b : Nat) :
    (c.advance a).advance b = c.advance (a + b) := by
  cases e : c.enable
  case false => simp [PulseCh.advance, e]
  case true =>
    by_cases ha : a = 0
    · subst ha; simp [pulse_advance_zero]
    · by_cases hb : b = 0
      · subst hb; simp [pulse_advance_zero]
      · have ba : (a == 0) = false := beq_eq_false_iff_ne.mpr ha
        have bb : (b == 0) = false := beq_eq_false_iff_ne.mpr hb
        have hab : a + b ≠ 0 := by omega
        have bab : (a + b == 0) = false := beq_eq_false_iff_ne.mpr hab
        simp [PulseCh.advance, e, ba, bb, bab, PulseCh.mk.injEq, PulseCh.period]
        -- everything is now explicit: fold the clock subterms
        generalize hpdef : (2048 - c.freq % 2048) * 4 = p
        have hml : c.freq % 2048 < 2048 := Nat.mod_lt _ (by omega)
        have hp : 0 < p := by omega
        generalize ht0def : (if c.timer = 0 then p else c.timer) = t0
        generalize hXdef : ((p - t0) + a) = X
        have hD : (p - t0) + (a + b) = X + b := by omega
        have hdecomp : p * (X / p) + X % p = X := Nat.div_add_mod X p
        have hr1lt : X % p < p := Nat.mod_lt _ hp
        generalize hs1 : X / p = s1
        generalize hr1def : X % p = r1
        rw [hs1, hr1def] at hdecomp
        rw [hr1def] at hr1lt
        by_cases hr1 : r1 = 0
        · -- first batch consumed a whole number of periods
          have et1 : (if r1 = 0 then p else p - r1) = p := by simp [hr1]
          have ht10 : (if r1 = 0 then p else p - r1) ≠ 0 := by omega
          simp [ht10]
          have ec1 : p - (if r1 = 0 then p else p - r1) = 0 := by
            rw [et1, Nat.sub_self]
          rw [ec1]
          simp only [Nat.zero_add]
          have hX0 : X = p * s1 := by omega
          have hS : (p - t0) + (a + b) = p * s1 + b := by rw [hD, hX0]
          have hdiv : (p * s1 + b) / p = s1 + b / p := by
            have h := Nat.add_mul_div_left b s1 hp
            rw [show p * s1 + b = b + p * s1 from by omega, h]
            exact Nat.add_comm _ _
          have hmod : (p * s1 + b) % p = b % p := by
            have h := Nat.add_mul_mod_self_left b p s1
            rw [show p * s1 + b = b + p * s1 from by omega]; exact h
          have hR : ((p - t0) + (a + b)) % p = b % p := by rw [hS]; exact hmod
          rw [hR]
          refine ⟨?_, ?_⟩
          · rfl
          · rw [hS]; omega
        · -- first batch ended mid-period; the leftover carries over
          have hr1pos : 0 < r1 := by omega
          have hle : r1 ≤ p := Nat.le_of_lt hr1lt
          have et1 : (if r1 = 0 then p else p - r1) = p - r1 := by simp [hr1]
          have ht10 : (if r1 = 0 then p else p - r1) ≠ 0 := by omega
          simp [ht10]
          have ec1 : p - (if r1 = 0 then p else p - r1) = r1 := by
            rw [et1]; omega
          rw [ec1]
          have hS : (p - t0) + (a + b) = p * s1 + (r1 + b) := by
            rw [hD]; omega
          have hdiv : (p * s1 + (r1 + b)) / p = s1 + (r1 + b) / p := by
            have h := Nat.add_mul_div_left (r1 + b) s1 hp
            rw [show p * s1 + (r1 + b) = (r1 + b) + p * s1 from by omega, h]
            exact Nat.add_comm _ _
          have hmod : (p * s1 + (r1 + b)) % p = (r1 + b) % p := by
            have h := Nat.add_mul_mod_self_left (r1 + b) p s1
            rw [show p * s1 + (r1 + b) = (r1 + b) + p * s1 from by omega]; exact h
          have hR : ((p - t0) + (a + b)) % p = (r1 + b) % p := by
            rw [hS]; exact hmod
          rw [hR]
          refine ⟨?_, ?_⟩
          · rfl
          · rw [hS]; omega

/-- Stepping preserves enable (pulse). -/
theorem pulse_advance_enable (c : PulseCh) (t : Nat) :
    (c.advance t).enable = c.enable := by
  unfold PulseCh.advance
  split <;> rfl

/-- Stepping preserves frequency (pulse). -/
theorem pulse_advance_freq (c : PulseCh) (t : Nat) :
    (c.advance t).freq = c.freq := by
  unfold PulseCh.advance
  split <;> rfl

/-- Stepping preserves duty (pulse). -/
theorem pulse_advance_duty (c : PulseCh) (t : Nat) :
    (c.advance t).duty = c.duty := by
  unfold PulseCh.advance
  split <;> rfl

/-- Stepping preserves volume (pulse). -/
theorem pulse_advance_vol (c : PulseCh) (t : Nat) :
    (c.advance t).vol = c.vol := by
  unfold PulseCh.advance
  split <;> rfl

/-- Stepping preserves enable (wave). -/
theorem wave_advance_enable (c : WaveCh) (t : Nat) :
    (c.advance t).enable = c.enable := by
  unfold WaveCh.advance
  split <;> rfl

/-- Stepping preserves frequency (wave). -/
theorem wave_advance_freq (c : WaveCh) (t : Nat) :
    (c.advance t).freq = c.freq := by
  unfold WaveCh.advance
  split <;> rfl

/-- Phase advance is additive (wave): same counting core as pulse,
    with `% 32` position tracking. -/
theorem wave_advance_additive (c : WaveCh) (a b : Nat) :
    (c.advance a).advance b = c.advance (a + b) := by
  cases e : c.enable
  case false => simp [WaveCh.advance, e]
  case true =>
    by_cases ha : a = 0
    · subst ha; simp [wave_advance_zero]
    · by_cases hb : b = 0
      · subst hb; simp [wave_advance_zero]
      · have ba : (a == 0) = false := beq_eq_false_iff_ne.mpr ha
        have bb : (b == 0) = false := beq_eq_false_iff_ne.mpr hb
        have hab : a + b ≠ 0 := by omega
        have bab : (a + b == 0) = false := beq_eq_false_iff_ne.mpr hab
        simp [WaveCh.advance, e, ba, bb, bab, WaveCh.mk.injEq, WaveCh.period]
        generalize hpdef : (2048 - c.freq % 2048) * 2 = p
        have hml : c.freq % 2048 < 2048 := Nat.mod_lt _ (by omega)
        have hp : 0 < p := by omega
        generalize ht0def : (if c.timer = 0 then p else c.timer) = t0
        generalize hXdef : ((p - t0) + a) = X
        have hD : (p - t0) + (a + b) = X + b := by omega
        have hdecomp : p * (X / p) + X % p = X := Nat.div_add_mod X p
        have hr1lt : X % p < p := Nat.mod_lt _ hp
        generalize hs1 : X / p = s1
        generalize hr1def : X % p = r1
        rw [hs1, hr1def] at hdecomp
        rw [hr1def] at hr1lt
        by_cases hr1 : r1 = 0
        · have et1 : (if r1 = 0 then p else p - r1) = p := by simp [hr1]
          have ht10 : (if r1 = 0 then p else p - r1) ≠ 0 := by omega
          simp [ht10]
          have ec1 : p - (if r1 = 0 then p else p - r1) = 0 := by
            rw [et1, Nat.sub_self]
          rw [ec1]
          simp only [Nat.zero_add]
          have hX0 : X = p * s1 := by omega
          have hS : (p - t0) + (a + b) = p * s1 + b := by omega
          have hdiv : (p * s1 + b) / p = s1 + b / p := by
            have h := Nat.add_mul_div_left b s1 hp
            rw [show p * s1 + b = b + p * s1 from by omega, h]
            exact Nat.add_comm _ _
          have hmod : (p * s1 + b) % p = b % p := by
            have h := Nat.add_mul_mod_self_left b p s1
            rw [show p * s1 + b = b + p * s1 from by omega]; exact h
          have hR : ((p - t0) + (a + b)) % p = b % p := by rw [hS]; exact hmod
          rw [hR]
          refine ⟨?_, ?_⟩
          · rfl
          · rw [hS]; omega
        · have et1 : (if r1 = 0 then p else p - r1) = p - r1 := by simp [hr1]
          have hle : r1 ≤ p := Nat.le_of_lt hr1lt
          have ht10 : (if r1 = 0 then p else p - r1) ≠ 0 := by omega
          simp [ht10]
          have ec1 : p - (if r1 = 0 then p else p - r1) = r1 := by
            rw [et1]; omega
          rw [ec1]
          have hS : (p - t0) + (a + b) = p * s1 + (r1 + b) := by omega
          have hdiv : (p * s1 + (r1 + b)) / p = s1 + (r1 + b) / p := by
            have h := Nat.add_mul_div_left (r1 + b) s1 hp
            rw [show p * s1 + (r1 + b) = (r1 + b) + p * s1 from by omega, h]
            exact Nat.add_comm _ _
          have hmod : (p * s1 + (r1 + b)) % p = (r1 + b) % p := by
            have h := Nat.add_mul_mod_self_left (r1 + b) p s1
            rw [show p * s1 + (r1 + b) = (r1 + b) + p * s1 from by omega]
            exact h
          have hR : ((p - t0) + (a + b)) % p = (r1 + b) % p := by
            rw [hS]; exact hmod
          rw [hR]
          refine ⟨?_, ?_⟩
          · rfl
          · rw [hS]; omega

/-! ## Noise LFSR additivity -/

/-- Splitting a noise batch: stepping `a + b` clicks equals stepping `a`
    then `b` from the intermediate state. Induction on the first batch;
    each unfolding exposes one `timer ≤ 1` step on both sides. -/
theorem noiseStepLoop_add (p : Nat) (w : Bool) (a b t l : Nat) :
    NoiseCh.noiseStepLoop p w (a + b) t l =
      NoiseCh.noiseStepLoop p w b (NoiseCh.noiseStepLoop p w a t l).1
        (NoiseCh.noiseStepLoop p w a t l).2 := by
  induction a generalizing t l with
  | zero => simp [NoiseCh.noiseStepLoop]
  | succ n ih =>
    have h : (n + 1) + b = (n + b) + 1 := by omega
    rw [h]
    cases w with
    | true =>
      simp only [NoiseCh.noiseStepLoop, ite_true]
      by_cases ht : t ≤ 1
      · simp only [ht, ite_true]
        exact ih _ _
      · simp only [ht, ite_false]
        exact ih _ _
    | false =>
      simp only [NoiseCh.noiseStepLoop]
      by_cases ht : t ≤ 1
      · simp only [ht, ite_true]
        exact ih _ _
      · simp only [ht, ite_false]
        exact ih _ _

/-- Push `.1` through `ite` (projection version of `snd_ite`). -/
theorem fst_ite (c : Prop) [Decidable c] (a b : Nat × Nat) :
    (if c then a else b).1 = if c then a.1 else b.1 := by
  by_cases h : c <;> simp [h]

/-- Powers of two are positive. -/
theorem two_pow_pos (n : Nat) : 0 < 2 ^ n := by
  induction n with
  | zero => decide
  | succ k ih => rw [Nat.pow_add_one]; exact Nat.mul_pos ih (by omega)

/-- The noise period is positive (`div ≥ 8`, `1 <<< shift ≥ 1`). -/
theorem noisePeriod_pos (c : NoiseCh) : 0 < NoiseCh.noisePeriod c := by
  have hshift : 0 < 1 <<< c.shift := by
    rw [Nat.one_shiftLeft]; exact two_pow_pos _
  unfold NoiseCh.noisePeriod
  split
  all_goals first | (exact Nat.mul_pos (by omega) hshift) | split
  all_goals first | (exact Nat.mul_pos (by omega) hshift) | split
  all_goals first | (exact Nat.mul_pos (by omega) hshift) | split
  all_goals (exact Nat.mul_pos (by omega) hshift)

/-- A noise batch starting from a live timer leaves a live timer. -/
theorem noiseStepLoop_timer_pos (p : Nat) (w : Bool) (a t l : Nat)
    (hp : 0 < p) (ht : 0 < t) :
    0 < (NoiseCh.noiseStepLoop p w a t l).1 := by
  induction a generalizing t l with
  | zero => simpa [NoiseCh.noiseStepLoop] using ht
  | succ n ih =>
    simp only [NoiseCh.noiseStepLoop, fst_ite]
    split
    · exact ih _ _ hp
    · exact ih _ _ (by omega)

/-- Phase advance is additive (noise): batch splitting via
    `noiseStepLoop_add`; config fields are untouched. -/
theorem noise_advance_additive (c : NoiseCh) (a b : Nat) :
    (c.advance a).advance b = c.advance (a + b) := by
  cases e : c.enable
  case false => simp [NoiseCh.advance, e]
  case true =>
    have hp : 0 < NoiseCh.noisePeriod c := noisePeriod_pos c
    have ht0pos : 0 < (if c.timer = 0 then c.noisePeriod else c.timer) := by
      by_cases ht0 : c.timer = 0 <;> simp [ht0] <;> first | exact hp | omega
    have houter : (NoiseCh.noiseStepLoop c.noisePeriod c.width a
        (if c.timer = 0 then c.noisePeriod else c.timer) c.lfsr).1 ≠ 0 := by
      have h := noiseStepLoop_timer_pos c.noisePeriod c.width a
        (if c.timer = 0 then c.noisePeriod else c.timer) c.lfsr hp ht0pos
      omega
    simp [NoiseCh.advance, e, NoiseCh.mk.injEq]
    simp only [houter, ite_false]
    simp only [NoiseCh.noisePeriod]
    refine ⟨?_, ?_⟩ <;> rw [noiseStepLoop_add] <;> rfl

/-! ## Duty tables -/

/-- Duty patterns are single bits. -/
theorem dutyPat_lt (d i : Nat) : dutyPat d i < 2 := by
  unfold dutyPat
  split
  all_goals omega

theorem dutyPat_12p5 : dutyPat 0 7 = 1 ∧ dutyPat 0 0 = 0 := by decide

theorem dutyPat_50 : dutyPat 2 0 = 1 ∧ dutyPat 2 1 = 0 ∧ dutyPat 2 5 = 1 := by
  decide

/-! ## Periods -/

/-- Lowest frequency: longest period. -/
theorem pulsePeriod_lo : PulseCh.period { freq := 0 } = 8192 := by decide

/-- Highest frequency: shortest period. -/
theorem pulsePeriod_hi : PulseCh.period { freq := 2047 } = 4 := by decide

/-- Periods are always positive (no silent divide-by-zero downstream). -/
theorem pulsePeriod_pos (c : PulseCh) : 0 < PulseCh.period c := by
  have hmod : c.freq % 2048 < 2048 := by omega
  unfold PulseCh.period
  omega

theorem wavePeriod_lo : WaveCh.period { freq := 0 } = 4096 := by decide

/-! ## DAC gating -/

/-- Disabled pulse channel is silent. -/
theorem pulseOut_disabled (c : PulseCh) (h : c.enable = false) :
    PulseCh.output c = 0 := by
  simp [PulseCh.output, h]

/-- Pulse with DAC off is silent. -/
theorem pulseOut_dacOff (c : PulseCh) (h : c.dac = false) :
    PulseCh.output c = 0 := by
  simp [PulseCh.output, h]

/-- Full-volume 50% pulse at phase 0 outputs 15. -/
theorem pulseOut_full :
    PulseCh.output { enable := true, dac := true, duty := 2, phase := 0, vol := 15 } = 15 := by
  decide

/-- Disabled wave channel is silent. -/
theorem waveOut_disabled (c : WaveCh) (h : c.enable = false) :
    WaveCh.output c = 0 := by
  simp [WaveCh.output, h]

/-- Volume code 0 mutes the wave channel. -/
theorem waveOut_vol0 (c : WaveCh) (hen : c.enable = true)
    (hdac : c.dac = true) (hv : c.volCode = 0) :
    WaveCh.output c = 0 := by
  simp [WaveCh.output, hen, hdac, hv]

/-- Disabled noise channel is silent. -/
theorem noiseOut_disabled (c : NoiseCh) (h : c.enable = false) :
    NoiseCh.output c = 0 := by
  simp [NoiseCh.output, h]

/-- Noise with a set output bit is silent. -/
theorem noiseOut_bitSet (c : NoiseCh) (hen : c.enable = true)
    (hdac : c.dac = true) (hodd : c.lfsr % 2 = 1) :
    NoiseCh.output c = 0 := by
  simp [NoiseCh.output, hen, hdac, hodd]

/-! ## Length + envelope -/

/-- Length expiry disables the pulse channel. -/
theorem pulseLen_expires :
    (({ len := 1, lenEnable := true, enable := true } : PulseCh)).lenTick.enable
      = false := by
  decide

/-- Length expiry clears the counter. -/
theorem pulseLen_zeroes :
    (({ len := 1, lenEnable := true, enable := true } : PulseCh)).lenTick.len
      = 0 := by
  decide

/-- Length disabled: length ticks preserve volume. -/
theorem pulseLen_holdVol (c : PulseCh) (h : c.lenEnable = false) :
    (c.lenTick).vol = c.vol := by
  simp [PulseCh.lenTick, h]

/-- Envelope with period 0 holds volume. -/
theorem pulseEnv_holdVol (c : PulseCh) (h : c.envPeriod = 0) :
    (c.envTick).vol = c.vol := by
  simp [PulseCh.envTick, h]

/-- Noise envelope with period 0 holds volume. -/
theorem noiseEnv_holdVol (c : NoiseCh) (h : c.envPeriod = 0) :
    (c.envTick).vol = c.vol := by
  simp [NoiseCh.envTick, h]

/-! ## Mixer -/

/-- Unpowered mixer is silent. -/
theorem mix_unpowered (s : ApuState) (h : s.powered = false) :
    ApuState.mix s = 0 := by
  simp [ApuState.mix, h]

/-- Silence bias at zero master volume. -/
theorem silence_zeroVol : (({ nr50 := 0 } : ApuState)).silence = -3840 := by
  decide

/-- Fresh APU is all-quiet. -/
theorem allQuiet_fresh : (({} : ApuState)).allQuiet = true := by decide

/-! ## Sample-clock constants -/

theorem sampleBase_is95 : ApuState.sampleBase = 95 := rfl

theorem sampleErrStep_is4804 : ApuState.sampleErrStep = 4804 := rfl

theorem sampleErrMax_is44100 : ApuState.sampleErrMax = 44100 := rfl

end GB
