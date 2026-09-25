/-
  LeanGameboy.Proofs.Interrupts — IE/IF dispatch priority contracts.

  `Interrupts.lean` was only imported for its priority statement.
  These pin the bit positions, the lowest-wins selection (generally
  for the first two levels, by instance elsewhere), vector addresses,
  and the raise/request interaction.
-/
import LeanGameboy.Interrupts

namespace GB

/-! ## Bit positions -/

theorem irq_bit_vblank : irqVBlank = 0 := rfl

theorem irq_bit_lcd : irqLCD = 1 := rfl

theorem irq_bit_timer : irqTimer = 2 := rfl

theorem irq_bit_serial : irqSerial = 3 := rfl

theorem irq_bit_joypad : irqJoypad = 4 := rfl

/-! ## Pending selection -/

/-- Nothing enabled and pending: nothing fires. -/
theorem pending_none : irqPending 0 0 = none := by decide

/-- VBlank wins over everything below it. -/
theorem pending_vblank : irqPending 0x1F 0x1F = some 0 := by decide

/-- LCD wins when VBlank is quiet. -/
theorem pending_lcd : irqPending 0x1F 0x06 = some 1 := by decide

/-- A masked interrupt never fires. -/
theorem pending_masked : irqPending 0x01 0x02 = none := by decide

/-- Timer fires when only it is pending. -/
theorem pending_timer : irqPending 0x04 0x04 = some 2 := by decide

/-- Bit 0 pending always selects VBlank, regardless of the rest. -/
theorem pending_bit0 (ie if_ : UInt8)
    (h : bitGet (ie &&& if_) 0 = true) :
    irqPending ie if_ = some 0 := by
  simp [irqPending, h]

/-- Bit 1 selects LCD when bit 0 is quiet. -/
theorem pending_bit1 (ie if_ : UInt8)
    (h0 : bitGet (ie &&& if_) 0 = false)
    (h1 : bitGet (ie &&& if_) 1 = true) :
    irqPending ie if_ = some 1 := by
  simp [irqPending, h0, h1]

/-- No masked bit set: nothing fires. -/
theorem pending_empty (ie if_ : UInt8) (h : ie &&& if_ = 0) :
    irqPending ie if_ = none := by
  simp [irqPending, h, bitGet, bitMask]

/-! ## Vectors -/

theorem vector_vblank : irqVector 0 = 0x40 := by decide

theorem vector_lcd : irqVector 1 = 0x48 := by decide

theorem vector_joypad : irqVector 4 = 0x60 := by decide

/-! ## Raise / acknowledge interaction -/

/-- Raising bit 2 sets it. -/
theorem raise_timer : bitGet (irqRaise 0x00 2) 2 = true := by decide

/-- Acknowledging clears a set bit. -/
theorem ack_clears : bitGet (irqAck 0xFF 3) 3 = false := by decide

/-- A raised timer interrupt is found by dispatch. -/
theorem raised_found : irqPending 0x04 (irqRaise 0x00 2) = some 2 := by
  decide

end GB
