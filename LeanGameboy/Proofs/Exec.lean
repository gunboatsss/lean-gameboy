/-
  LeanGameboy.Proofs.Exec — SM83 execution vectors.

  Convention (mirroring `LeanAGB.Proofs.Spec`): each vector is a closed
  `decide` over `exec`, so the kernel replays the documented semantics
  on every build. This lifts the `Tests/Smoke` magic constants to
  checked vectors and pins per-arm behavior where `Proofs/Bus` only
  pins cycle lower bounds. States use `{}`-defaults so the kernel never
  reduces large arrays (`busRead` on empty ROM yields `0xFF`).
-/
import LeanGameboy.Bus

namespace GB

/-- Concrete test state: registers only, empty machine. -/
def execState (r : Regs) : GBState := { ({} : GBState) with regs := r }

/-! ## Flag ops -/

theorem exec_nop_pc : (exec {} .Nop 0x100).1.regs.pc = 0x101 := by decide

theorem exec_nop_cost : (exec {} .Nop 0x100).2 = 1 := by decide

theorem exec_cpl :
    (exec (execState { a := 0x00 }) .Cpl 0x100).1.regs.a = 0xFF ∧
    (exec (execState { a := 0x00 }) .Cpl 0x100).1.regs.n = true ∧
    (exec (execState { a := 0x00 }) .Cpl 0x100).1.regs.hf = true := by
  decide

theorem exec_scf : (exec {} .Scf 0x100).1.regs.cf = true := by decide

theorem exec_ccf_set : (exec {} .Ccf 0x100).1.regs.cf = true := by decide

theorem exec_ccf_clear :
    (exec (execState { cf := true }) .Ccf 0x100).1.regs.cf = false := by
  decide

/-! ## Rotates -/

/-- `RLCA` on `0x85`: rotates bit 7 out, clears Z. -/
theorem exec_rlca :
    (exec (execState { a := 0x85 }) .Rlca 0x100).1.regs.a = 0x0B ∧
    (exec (execState { a := 0x85 }) .Rlca 0x100).1.regs.cf = true ∧
    (exec (execState { a := 0x85 }) .Rlca 0x100).1.regs.z = false := by
  decide

/-- `RRCA` on `0x01`: bit 0 wraps to bit 7. -/
theorem exec_rrca :
    (exec (execState { a := 0x01 }) .Rrca 0x100).1.regs.a = 0x80 ∧
    (exec (execState { a := 0x01 }) .Rrca 0x100).1.regs.cf = true := by
  decide

/-! ## Increments / decrements -/

/-- `INC B` half-carries `0x0F → 0x10`. -/
theorem exec_inc_b_half :
    (exec (execState { b := 0x0F }) (.IncR8 .B) 0x100).1.regs.b = 0x10 ∧
    (exec (execState { b := 0x0F }) (.IncR8 .B) 0x100).1.regs.hf = true ∧
    (exec (execState { b := 0x0F }) (.IncR8 .B) 0x100).1.regs.z = false := by
  decide

/-- `INC B` wraps `0xFF → 0x00` with Z set. -/
theorem exec_inc_b_wrap :
    (exec (execState { b := 0xFF }) (.IncR8 .B) 0x100).1.regs.b = 0x00 ∧
    (exec (execState { b := 0xFF }) (.IncR8 .B) 0x100).1.regs.z = true := by
  decide

/-- `DEC C` sets N. -/
theorem exec_dec_c :
    (exec (execState { c := 0x01 }) (.DecR8 .C) 0x100).1.regs.c = 0x00 ∧
    (exec (execState { c := 0x01 }) (.DecR8 .C) 0x100).1.regs.z = true ∧
    (exec (execState { c := 0x01 }) (.DecR8 .C) 0x100).1.regs.n = true := by
  decide

/-- `INC BC` wraps `0xFFFF → 0x0000`. -/
theorem exec_inc16_wrap :
    (exec (execState { b := 0xFF, c := 0xFF }) (.IncR16 .BC) 0x100).1.regs.bc
      = 0x0000 := by
  decide

/-! ## Loads -/

/-- `LD A,B` copies. -/
theorem exec_ldrr :
    (exec (execState { b := 0x42 }) (.LdRR .A .B) 0x100).1.regs.a
      = 0x42 := by
  decide

/-! ## ALU -/

/-- `ADD A,B`: the smoke-test `0x45 + 0x38 = 0x7D` at `exec` level. -/
theorem exec_alu_add :
    (exec (execState { a := 0x45, b := 0x38 }) (.AluR .Add .B) 0x100).1.regs.a
      = 0x7D := by
  decide

/-! ## Jumps -/

/-- Unconditional `JR` on an empty ROM reads offset `0xFF` (−1). -/
theorem exec_jr_uncond : (exec {} (.Jr none) 0x100).1.regs.pc = 0x101 := by
  decide

theorem exec_jr_uncond_cost : (exec {} (.Jr none) 0x100).2 = 3 := by decide

/-- `JR NZ` taken when Z is clear. -/
theorem exec_jr_nz_taken :
    (exec (execState { z := false }) (.Jr (.some .NZ)) 0x100).1.regs.pc
      = 0x101 := by
  decide

/-- `JR NZ` falls through when Z is set (cheaper). -/
theorem exec_jr_nz_nottaken :
    (exec (execState { z := true }) (.Jr (.some .NZ)) 0x100).1.regs.pc
      = 0x102 ∧
    (exec (execState { z := true }) (.Jr (.some .NZ)) 0x100).2 = 2 := by
  decide

/-! ## Interrupt master enable -/

theorem exec_di : (exec {} .Di 0x100).1.regs.ime = false := by decide

theorem exec_ei : (exec {} .Ei 0x100).1.regs.eiDelay = true := by decide

/-! ## 16-bit ADD -/

/-- `ADD HL,BC` half-carries `0x0FFF + 1`. -/
theorem exec_addhl_half :
    (exec (execState { h := 0x0F, l := 0xFF, b := 0x00, c := 0x01 })
      (.AddHL .BC) 0x100).1.regs.hl = 0x1000 ∧
    (exec (execState { h := 0x0F, l := 0xFF, b := 0x00, c := 0x01 })
      (.AddHL .BC) 0x100).1.regs.hf = true ∧
    (exec (execState { h := 0x0F, l := 0xFF, b := 0x00, c := 0x01 })
      (.AddHL .BC) 0x100).1.regs.cf = false := by
  decide

end GB
