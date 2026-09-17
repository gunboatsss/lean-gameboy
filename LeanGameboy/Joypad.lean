/-
  LeanGameboy.Joypad — P1 (0xFF00) button matrix.
-/
import LeanGameboy.Basic

namespace GB

/-- Joypad button state (`true` = pressed). -/
structure JoypadState where
  right : Bool := false
  left : Bool := false
  up : Bool := false
  down : Bool := false
  a : Bool := false
  b : Bool := false
  select : Bool := false
  start : Bool := false
  -- P1 select bits (true = selected / low on hardware)
  selButtons : Bool := false
  selDpad : Bool := false
deriving DecidableEq, Repr

namespace JoypadState

/-- Read the P1 register (bits 0-3 are active-low). -/
def read (j : JoypadState) : UInt8 :=
  let lo : UInt8 :=
    if j.selButtons && j.selDpad then 0x0F
    else if j.selButtons then
      (if j.start then 0 else 8) ||| (if j.select then 0 else 4) |||
      (if j.b then 0 else 2) ||| (if j.a then 0 else 1) ||| 0
    else if j.selDpad then
      (if j.down then 0 else 8) ||| (if j.up then 0 else 4) |||
      (if j.left then 0 else 2) ||| (if j.right then 0 else 1) ||| 0
    else 0x0F
  let hi : UInt8 :=
    0xC0 ||| (if !j.selButtons then 0x20 else 0) |||
    (if !j.selDpad then 0x10 else 0)
  hi ||| (lo &&& 0x0F)

/-- Write P1: only bits 4/5 are writable. -/
def write (j : JoypadState) (v : UInt8) : JoypadState :=
  { j with selButtons := !bitGet v 5, selDpad := !bitGet v 4 }

/-- Any button currently pressed (for edge-triggered IRQ). -/
def anyPressed (j : JoypadState) : Bool :=
  j.right || j.left || j.up || j.down || j.a || j.b || j.select || j.start

end JoypadState

end GB
