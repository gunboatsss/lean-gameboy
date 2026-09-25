/-
  LeanAGB.Proofs.Irq — interrupt gating and entry/exit vectors.

  There is no GBA hardware priority (the BIOS polls `IF`; see
  `serviceIrq`): entry fires on any pending IRQ. `Proofs/Mode` pins
  the mode codec, bank isolation, and entry roundtrips; here are the
  pending gate, the unhalt/ime side effects, and closed entry/exit
  vectors. (`get 15` needs a full register file, so the PC pins are
  instances over a 16-wide file rather than universal.)
-/
import LeanAGB.Bus

namespace AGB

/-! ## Pending gate -/

/-- Masked-off master: nothing is pending. -/
theorem pending_ime_off (q : AgbIrq) (h : q.ime = false) :
    irqPending q = false := by
  simp [irqPending, h]

/-- No enabled bit set: nothing is pending. -/
theorem pending_empty (q : AgbIrq) (h : q.ie &&& q.if_ = 0) :
    irqPending q = false := by
  simp [irqPending, h]

theorem pending_vblank :
    irqPending { ie := 1, if_ := 1, ime := true } = true := by
  decide

theorem pending_ime_gates :
    irqPending { ie := 1, if_ := 1, ime := false } = false := by
  decide

/-! ## Entry/exit side effects (structural) -/

/-- IRQ entry releases a halt. -/
theorem serviceIrq_unhalts (s : AGBState) :
    (serviceIrq s).halted = false := rfl

/-- SWI entry releases a halt. -/
theorem serviceSwi_unhalts (s : AGBState) (a : UInt32) :
    (serviceSwi s a).halted = false := rfl

/-- Exception return preserves halt, IRQ state, and time. -/
theorem excReturn_halts (s : AGBState) (p l : UInt32) :
    (excReturn s p l).halted = s.halted := rfl

theorem excReturn_irq (s : AGBState) (p l : UInt32) :
    (excReturn s p l).irq = s.irq := rfl

/-! ## Closed entry/exit vectors (16-wide register file) -/

/-- Concrete file: 16 zero registers in SYS mode. -/
def irqRegs : ArmRegs :=
  { r := Array.replicate 16 0, cpsr := 0x3F }

def irqState : AGBState :=
  { ({} : AGBState) with regs := irqRegs }

/-- IRQ entry vectors PC at `0x18`. -/
theorem entry_pc : (serviceIrq irqState).regs.get 15 = 0x18 := by
  decide

/-- IRQ entry drops the halt flag. -/
theorem entry_halted : (serviceIrq irqState).halted = false := by
  decide

/-- SWI entry vectors PC at `0x08`. -/
theorem swi_pc (a : UInt32) :
    (serviceSwi irqState a).regs.get 15 = 0x08 := by
  rfl

/-- Exception return restores the passed PC. -/
theorem exit_pc (p l : UInt32) :
    (excReturn irqState p l).regs.get 15 = l := by
  rfl

end AGB
