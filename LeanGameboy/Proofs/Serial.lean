/-
  LeanGameboy.Proofs.Serial — link-cable stub state machine.

  `Proofs/Spec` pins append-only output; here are the transfer
  dynamics: idle identity, countdown preservation, completion effects,
  transfer arming, and interrupt acknowledgement.
-/
import LeanGameboy.Serial

namespace GB

namespace SerialState

/-! ## Idle: no transfer, no-op -/

/-- With no transfer running, stepping is the identity. -/
theorem step_idle (s : SerialState) (dots : Nat) (h : s.dots = 0) :
    s.step dots = s := by
  have e : (s.dots == 0) = true := by rw [h]; decide
  unfold step
  rw [ite_eq_left e]

/-! ## Countdown: ticks down, output and IRQ untouched -/

/-- The counter ticks down. -/
theorem step_countdown_dots (s : SerialState) (dots : Nat)
    (hne : s.dots ≠ 0) (hlt : dots < s.dots) :
    (s.step dots).dots = s.dots - dots := by
  have e0 : ¬ ((s.dots == 0) = true) := fun hc => hne (beq_iff_eq.mp hc)
  unfold step
  rw [ite_eq_right e0, ite_eq_left hlt]

/-- Output is untouched while counting down. -/
theorem step_countdown_out (s : SerialState) (dots : Nat)
    (hne : s.dots ≠ 0) (hlt : dots < s.dots) :
    (s.step dots).out = s.out := by
  have e0 : ¬ ((s.dots == 0) = true) := fun hc => hne (beq_iff_eq.mp hc)
  unfold step
  rw [ite_eq_right e0, ite_eq_left hlt]

/-- No interrupt while counting down. -/
theorem step_countdown_irq (s : SerialState) (dots : Nat)
    (hne : s.dots ≠ 0) (hlt : dots < s.dots) :
    (s.step dots).irq = s.irq := by
  have e0 : ¬ ((s.dots == 0) = true) := fun hc => hne (beq_iff_eq.mp hc)
  unfold step
  rw [ite_eq_right e0, ite_eq_left hlt]

/-! ## Completion: byte captured, IRQ raised -/

/-- The sent byte lands in the log. -/
theorem step_complete_out (s : SerialState) (dots : Nat)
    (hne : s.dots ≠ 0) (hle : s.dots ≤ dots) :
    (s.step dots).out = s.out.push s.sb := by
  have e0 : ¬ ((s.dots == 0) = true) := fun hc => hne (beq_iff_eq.mp hc)
  have e1 : ¬ dots < s.dots := by omega
  unfold step
  rw [ite_eq_right e0, ite_eq_right e1]

/-- Completion raises the serial interrupt. -/
theorem step_complete_irq (s : SerialState) (dots : Nat)
    (hne : s.dots ≠ 0) (hle : s.dots ≤ dots) :
    (s.step dots).irq = true := by
  have e0 : ¬ ((s.dots == 0) = true) := fun hc => hne (beq_iff_eq.mp hc)
  have e1 : ¬ dots < s.dots := by omega
  unfold step
  rw [ite_eq_right e0, ite_eq_right e1]

/-- Completion reloads SB with idle bits and stops the clock. -/
theorem step_complete_sb (s : SerialState) (dots : Nat)
    (hne : s.dots ≠ 0) (hle : s.dots ≤ dots) :
    (s.step dots).sb = 0xFF ∧ (s.step dots).dots = 0 := by
  have e0 : ¬ ((s.dots == 0) = true) := fun hc => hne (beq_iff_eq.mp hc)
  have e1 : ¬ dots < s.dots := by omega
  unfold step
  rw [ite_eq_right e0, ite_eq_right e1]
  exact ⟨rfl, rfl⟩

/-! ## Arming -/

/-- Internal clock + idle starts a transfer. -/
theorem maybeStart_arms :
    (({ sc := 0x81 } : SerialState)).maybeStart.dots = 8 * 512 := by
  decide

/-- Without the clock bit nothing starts. -/
theorem maybeStart_noClock :
    (({ sc := 0x80 } : SerialState)).maybeStart.dots = 0 := by
  decide

/-- A running transfer is never restarted. -/
theorem maybeStart_busy :
    (({ sc := 0x81, dots := 100 } : SerialState)).maybeStart.dots
      = 100 := by
  decide

/-! ## Acknowledgement -/

/-- Ack clears the interrupt and nothing else moves. -/
theorem ackIrq_clears (s : SerialState) : s.ackIrq.irq = false := rfl

theorem ackIrq_out (s : SerialState) : s.ackIrq.out = s.out := rfl

theorem ackIrq_sb (s : SerialState) : s.ackIrq.sb = s.sb := rfl

end SerialState

end GB
