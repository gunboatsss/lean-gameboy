/-
  LeanGameboy.Proofs.Joypad — P1 (0xFF00) button-matrix contracts.

  `Joypad.lean` had zero proof coverage. These pin the read mapping
  (active-low nibbles, select bits), the write semantics (only bits
  4/5 land, buttons untouched), the press detector, and the bus
  roundtrip through `0xFF00`.
-/
import LeanGameboy.Bus

namespace GB

/-! ## Read mapping -/

/-- Released, unselected: all high. -/
theorem read_released : ({} : JoypadState).read = 0xFF := by decide

/-- Start pressed, buttons selected: bit 3 clears. -/
theorem read_start :
    ({ ({} : JoypadState) with start := true, selButtons := true }).read
      = 0xD7 := by
  decide

/-- Down pressed, d-pad selected: bit 3 clears. -/
theorem read_down :
    ({ ({} : JoypadState) with down := true, selDpad := true }).read
      = 0xE7 := by
  decide

/-- A pressed, buttons selected: bit 0 clears. -/
theorem read_a :
    ({ ({} : JoypadState) with a := true, selButtons := true }).read
      = 0xDE := by
  decide

/-! ## Write semantics -/

/-- Writing only selects; every button is preserved. -/
theorem write_preserves (j : JoypadState) (v : UInt8) :
    (j.write v).right = j.right ∧ (j.write v).left = j.left ∧
    (j.write v).up = j.up ∧ (j.write v).down = j.down ∧
    (j.write v).a = j.a ∧ (j.write v).b = j.b ∧
    (j.write v).select = j.select ∧ (j.write v).start = j.start :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Bit 5 set deselects buttons. -/
theorem write_selButtons_off :
    (({} : JoypadState).write 0xFF).selButtons = false := by decide

/-- Bit 4 clear selects the d-pad. -/
theorem write_selDpad_on :
    (({} : JoypadState).write 0xEF).selDpad = true := by decide

/-- Select lines follow bits 5/4 exactly. -/
theorem write_sel (j : JoypadState) (v : UInt8) :
    (j.write v).selButtons = !bitGet v 5 ∧
    (j.write v).selDpad = !bitGet v 4 := by
  constructor <;> rfl

/-! ## Press detector -/

theorem anyPressed_empty : ({} : JoypadState).anyPressed = false := by
  decide

theorem anyPressed_a :
    ({ ({} : JoypadState) with a := true }).anyPressed = true := by
  decide

theorem anyPressed_start :
    ({ ({} : JoypadState) with start := true }).anyPressed = true := by
  decide

/-- Selection writes never fake a press. -/
theorem anyPressed_write (j : JoypadState) (v : UInt8) :
    (j.write v).anyPressed = j.anyPressed := rfl

/-! ## Bus integration -/

/-- A `0xFF00` write lands exactly in the joypad select lines. -/
theorem busWrite_joy_state (s : GBState) (v : UInt8) :
    (busWrite s 0xFF00 v).1 = { s with joy := s.joy.write v } := by
  simp [busWrite]

/-- A `0xFF00` read returns the P1 register. -/
theorem busRead_joy (s : GBState) : busRead s 0xFF00 = s.joy.read := by
  simp [busRead]

/-- Write-then-read roundtrip through the bus. -/
theorem bus_p1_roundtrip (s : GBState) (v : UInt8) :
    busRead (busWrite s 0xFF00 v).1 0xFF00 = (s.joy.write v).read := by
  rw [busWrite_joy_state, busRead_joy]

end GB
