/-
  LeanGameboy.Proofs.Apu — channel phase-step frame properties.

  Stepping never alters channel configuration (only phase/timer
  positions), and zero-stepping is the identity. These pin the frame
  that the bulk O(1) phase math — and the phase-debt batching built
  on it — must preserve.

  NOTE (open algebraic goal): full additivity
  `advance (advance c a) b = advance c (a + b)` holds by construction
  (phase-accumulator counting; validated empirically by Blargg +
  bit-identical Tetris runs) but its div/mod composition proof is
  deferred — the `||`/`==` guard residue resists uniform automation.
-/
import LeanGameboy.Apu

namespace GB

/-- Zero-stepping is the identity (pulse). -/
theorem pulse_advance_zero (c : PulseCh) : c.advance 0 = c := by
  simp [PulseCh.advance]

/-- Zero-stepping is the identity (wave). -/
theorem wave_advance_zero (c : WaveCh) : c.advance 0 = c := by
  simp [WaveCh.advance]

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

end GB
