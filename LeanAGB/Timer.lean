/- LeanAGB.Timer — 4-channel cascade timers (milestone: prescaled counters). -/
namespace AGB
structure AgbTimer where
  reload : UInt16 := 0
  cnt : UInt16 := 0
  ctrl : UInt16 := 0  -- bit7 enable, bit2 count-up, bits0-1 prescale
  acc : Nat := 0      -- prescaler debt in cycles
deriving DecidableEq, Repr
structure AgbTimers where
  ch : Array AgbTimer := Array.replicate 4 {}
deriving DecidableEq, Repr
/-- Prescaler divisor: 00=1 01=64 10=256 11=1024. -/
def timerDiv (ctrl : UInt16) : Nat :=
  match (ctrl.toNat >>> 0) &&& 0x3 with
  | 1 => 64 | 2 => 256 | 3 => 1024 | _ => 1
end AGB
