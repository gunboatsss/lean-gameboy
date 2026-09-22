/-
  LeanGameboy.Proofs.Halt — the halt-bug model, machine-checked.

  Double-`halt` with `IME == 0` and a pending interrupt spins on the
  second `halt` (PC frozen, bug re-armed); a lone fall-through arms
  the bug and advances once; bugged immediates shift down one byte
  (the repeated byte is re-read as the operand); bugged fall-through
  advances `len - 1`. Together these are exactly the mechanism the
  `double-halt-cancel` test ROM validates empirically
  (`FATE: RST $38`, inhibited return address). The push side is closed
  in `Proofs/Stack.lean`: `serviceIrq_pushes_pc` retrieves exactly the
  inhibited PC from an HRAM stack, and `exec_rst_pushes` pins the
  `RST`-instruction push (bug-armed: `pc + len - 1`).
-/
import LeanGameboy.Bus

namespace GB

/-- Double-halt spin: with the bug armed, `HALT` re-reads itself
    forever (PC fixed, bug stays armed). -/
theorem halt_spin (s : GBState) (pc : UInt16)
    (hbug : s.haltBug = true)
    (hime : s.regs.ime = false)
    (hb : ∃ b, irqPending s.ie s.if_ = some b) :
    ((exec s .Halt pc).1.regs.pc = pc) ∧
    ((exec s .Halt pc).1.haltBug = true) := by
  obtain ⟨b, hb⟩ := hb
  simp only [exec, hb, hbug, hime, reduceCtorEq, ite_true, ite_false]
  refine ⟨?_, ?_⟩ <;> trivial

/-- Single fall-through arms the bug and advances exactly once. -/
theorem halt_arms (s : GBState) (pc : UInt16)
    (hbug : s.haltBug = false)
    (hime : s.regs.ime = false)
    (hb : ∃ b, irqPending s.ie s.if_ = some b) :
    ((exec s .Halt pc).1.regs.pc = pc + 1) ∧
    ((exec s .Halt pc).1.haltBug = true) := by
  obtain ⟨b, hb⟩ := hb
  simp only [exec, hb, hbug, hime, reduceCtorEq, ite_false]
  refine ⟨?_, ?_⟩ <;> trivial

/-- Bugged `LD B,n` loads the repeated byte (from `pc`, not `pc+1`). -/
theorem bugged_imm8 (s : GBState) (pc : UInt16)
    (hbug : s.haltBug = true) :
    (exec s (.LdR8Imm .B) pc).1.regs.b = busRead s pc := by
  simp only [exec, setR8, hbug, ite_true]

/-- Bugged fall-through advances `len - 1` (one inhibited increment). -/
theorem bugged_nextpc (s : GBState) (pc : UInt16)
    (hbug : s.haltBug = true) :
    (exec s (.LdR8Imm .B) pc).1.regs.pc =
      pc + w16 (Instr.len (.LdR8Imm .B)) - 1 := by
  simp only [exec, setR8, hbug, ite_true]

end GB
