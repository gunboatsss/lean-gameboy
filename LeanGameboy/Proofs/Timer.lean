/-
  LeanGameboy.Proofs.Timer — timer step properties.

  The bulk O(1) update is exact by construction; these pin its
  edge cases: zero-step identity, disabled-TAC stability, and
  interrupt acknowledgement.
-/
import LeanGameboy.Timer

namespace GB

/-- Zero cycles: identity. -/
theorem timer_step_zero (t : TimerState) : t.step 0 = t := rfl

/-- With TAC disabled, TIMA never changes. -/
theorem timer_disabled_tima (t : TimerState) (m : Nat)
    (h : (t.tac.toNat / 4) % 2 == 0) :
    (t.step m).tima = t.tima := by
  have h' : (t.tac.toNat / 4) % 2 = 0 := by simpa using h
  unfold TimerState.step
  split
  · rfl
  · simp [h']

/-- With TAC disabled, no interrupt is raised. -/
theorem timer_disabled_irq (t : TimerState) (m : Nat)
    (h : (t.tac.toNat / 4) % 2 == 0) (hirq : t.irq = false) :
    (t.step m).irq = false := by
  have h' : (t.tac.toNat / 4) % 2 = 0 := by simpa using h
  unfold TimerState.step
  split
  · simp [hirq]
  · simp [h', hirq]

/-- Acknowledging clears the request. -/
theorem timer_ack (t : TimerState) : t.ackIrq.irq = false := rfl

end GB
