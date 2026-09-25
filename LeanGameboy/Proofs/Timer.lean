/-
  LeanGameboy.Proofs.Timer — timer step properties.

  The bulk O(1) update is exact by construction; these pin its
  edge cases: zero-step identity, disabled-TAC stability, frequency
  selection, DIV behavior, overflow reload, and interrupt
  acknowledgement.
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
  unfold TimerState.step TimerState.stepDots
  split
  · rfl
  · simp [h']

/-- With TAC disabled, no interrupt is raised. -/
theorem timer_disabled_irq (t : TimerState) (m : Nat)
    (h : (t.tac.toNat / 4) % 2 == 0) (hirq : t.irq = false) :
    (t.step m).irq = false := by
  have h' : (t.tac.toNat / 4) % 2 = 0 := by simpa using h
  unfold TimerState.step TimerState.stepDots
  split
  · simp [hirq]
  · simp [h', hirq]

/-- Acknowledging clears the request. -/
theorem timer_ack (t : TimerState) : t.ackIrq.irq = false := rfl

/-! ## Frequency selection -/

/-- TAC `00` flies at 4096 Hz (divider bit 9). -/
theorem freqBit_4096 : TimerState.freqBit 0x00 = 9 := by decide

/-- TAC `01` flies at 262144 Hz (divider bit 3). -/
theorem freqBit_fast : TimerState.freqBit 0x01 = 3 := by decide

/-- TAC `10` flies at 65536 Hz (divider bit 5). -/
theorem freqBit_mid : TimerState.freqBit 0x02 = 5 := by decide

/-- TAC `11` flies at 16384 Hz (divider bit 7). -/
theorem freqBit_slow : TimerState.freqBit 0x03 = 7 := by decide

/-- Only the low two TAC bits select the frequency. -/
theorem freqBit_masked : TimerState.freqBit 0x04 = 9 := by decide

/-- Bit set and enabled: the AND level is high. -/
theorem andLevel_on : TimerState.andLevel 512 0x04 = true := by decide

/-- Disabled: the AND level is low even with the bit set. -/
theorem andLevel_off : TimerState.andLevel 512 0x00 = false := by decide

/-- Bit clear: the AND level is low even when enabled. -/
theorem andLevel_bitClear : TimerState.andLevel 0 0x04 = false := by decide

/-! ## DIV reads -/

theorem div_zero : ({} : TimerState).div = 0 := by decide

theorem div_256 : ({ divInternal := 256 } : TimerState).div = 1 := by decide

theorem div_max : ({ divInternal := 0xFFFF } : TimerState).div = 0xFF := by
  decide

/-! ## Overflow reload -/

/-- TIMA `0xFF` plus one 4096 Hz edge reloads TMA and raises IRQ. -/
theorem stepDots_overflow_reload :
    (({ tac := 0x04, tima := 0xFF, tma := 0x42 } : TimerState)).stepDots 1024
      = { divInternal := 1024, tima := 0x42, tma := 0x42, tac := 0x04,
          prevAnd := false, irq := true } := by
  decide

/-- One edge below overflow just increments, no IRQ. -/
theorem stepDots_increment :
    (({ tac := 0x04, tima := 0xFE } : TimerState)).stepDots 1024
      = { divInternal := 1024, tima := 0xFF, tma := 0, tac := 0x04,
          prevAnd := false, irq := false } := by
  decide

/-! ## DIV writes -/

/-- Writing DIV resets the internal counter. -/
theorem writeDiv_zero (t : TimerState) : t.writeDiv.divInternal = 0 := rfl

/-- Writing DIV preserves the reload and control registers. -/
theorem writeDiv_preserves (t : TimerState) :
    t.writeDiv.tma = t.tma ∧ t.writeDiv.tac = t.tac := ⟨rfl, rfl⟩

/-- Zero dots at any level: identity. -/
theorem stepDots_zero (t : TimerState) : t.stepDots 0 = t := rfl

end GB
