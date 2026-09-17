/-
  LeanGameboy.Serial — SB/SC link cable stub.

  Implements the internal-clock transfer well enough for Blargg test
  ROMs (which use the serial port for test-result output): transmitted
  bytes are captured into `out` instead of going over a link cable.
-/
import LeanGameboy.Basic

namespace GB

/-- Serial port state. -/
structure SerialState where
  sb : UInt8 := 0
  sc : UInt8 := 0
  dots : Nat := 0      -- dots remaining in the current transfer
  out : Array UInt8 := #[]
  irq : Bool := false
deriving Repr

namespace SerialState

/-- Start a transfer if SC requests the internal clock. -/
def maybeStart (s : SerialState) : SerialState :=
  if bitGet s.sc 7 && bitGet s.sc 0 && s.dots == 0 then
    { s with dots := 8 * 512 }  -- 8192 Hz → 512 dots per bit
  else s

/-- Advance the serial port by `dots` T-cycles. -/
def step (s : SerialState) (dots : Nat) : SerialState :=
  if s.dots == 0 then s
  else if dots < s.dots then { s with dots := s.dots - dots }
  else
    -- transfer completes: slave would shift in 0xFF bits
    { s with
      sb := 0xFF
      sc := bitClear s.sc 7
      dots := 0
      out := s.out.push s.sb
      irq := true }
      -- note: `out` captures the byte the game sent (Blargg protocol)

/-- Acknowledge the serial interrupt. -/
def ackIrq (s : SerialState) : SerialState :=
  { s with irq := false }

end SerialState

end GB
