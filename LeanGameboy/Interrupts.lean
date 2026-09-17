/-
  LeanGameboy.Interrupts — IE/IF handling and dispatch priority.

  Priority (low bit wins): VBlank 0, LCD 1, Timer 2, Serial 3, Joypad 4.
  Vectors: 0x40 + 8 * bit.
-/
import LeanGameboy.Basic

namespace GB

/-- Interrupt bit positions. -/
def irqVBlank : Nat := 0
def irqLCD : Nat := 1
def irqTimer : Nat := 2
def irqSerial : Nat := 3
def irqJoypad : Nat := 4

/-- Lowest pending enabled interrupt, if any. -/
def irqPending (ie if_ : UInt8) : Option Nat :=
  let masked := ie &&& if_
  if bitGet masked 0 then some 0
  else if bitGet masked 1 then some 1
  else if bitGet masked 2 then some 2
  else if bitGet masked 3 then some 3
  else if bitGet masked 4 then some 4
  else none

/-- Vector address for an interrupt bit. -/
def irqVector (bit : Nat) : UInt16 :=
  w16 (0x40 + 8 * bit)

/-- Request an interrupt (set an IF bit). -/
def irqRaise (if_ : UInt8) (bit : Nat) : UInt8 :=
  bitSet if_ bit

/-- Acknowledge an interrupt (clear an IF bit). -/
def irqAck (if_ : UInt8) (bit : Nat) : UInt8 :=
  bitClear if_ bit

end GB
