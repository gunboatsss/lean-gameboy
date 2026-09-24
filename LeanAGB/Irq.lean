/- LeanAGB.Irq — IE/IF/IME + master dispatch helper. -/
import LeanAGB.Basic
namespace AGB
structure AgbIrq where
  ie : UInt16 := 0
  if_ : UInt16 := 0
  ime : Bool := false
deriving DecidableEq, Repr
def irqPending (q : AgbIrq) : Bool :=
  q.ime && ((q.ie &&& q.if_) != 0)
end AGB
