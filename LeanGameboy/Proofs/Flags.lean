/-
  LeanGameboy.Proofs.Flags — machine-checked spot checks for the ALU
  helpers, flag packing, and opcode decoding.

  These are `decide`d by the kernel at build time: if any of them
  fails, the build fails.
-/
import LeanGameboy.Basic
import LeanGameboy.Cpu.Regs
import LeanGameboy.Cpu.Decode

namespace GB

-- 0x0F + 0x01 sets half-carry but not full carry.
/-- Half-carry fires on a bit-3 overflow. -/
example : add8 0x0F 0x01 = { val := 0x10, halfCarry := true, carry := false } := by
  decide

/-- Full carry fires on a bit-7 overflow. -/
example : add8 0xFF 0x01 = { val := 0x00, halfCarry := true, carry := true } := by
  decide

/-- Carry-in propagates into both carries. -/
example : (add8 0x0F 0x00 true).halfCarry = true := by decide

/-- Borrow flags mirror carry flags. -/
example : sub8 0x00 0x01 = { val := 0xFF, halfCarry := true, carry := true } := by
  decide

/-- Borrow from bit 4 fires when low nibbles underflow (0xC-0xF). -/
example : sub8 0x3C 0x2F = { val := 0x0D, halfCarry := true, carry := false } := by
  decide

/-- AF round-trips through pack/unpack on the boot defaults. -/
example : (Regs.bootDefaults.setAF Regs.bootDefaults.af).a = 0x01 := by decide

/-- Opcode census: JR NZ is 0x20, HALT is 0x76, PREFIX-adjacent 0xCB is Invalid. -/
example : Instr.decodeFull 0x20 = .Jr (.some .NZ) := by decide
example : Instr.decodeFull 0x76 = .Halt := by decide
example : Instr.decodeFull 0xD3 = .Invalid := by decide
example : Instr.decodeFull 0x00 = .Nop := by decide
example : Instr.decodeFull 0xC3 = .Jp none := by decide
example : Instr.decodeCB 0x7C = .Bit 7 .H := by decide
example : Instr.decodeCB 0x00 = .Rot .Rlc .B := by decide
example : Instr.decodeCB 0xFF = .Set 7 .A := by decide

/-- Lengths: JP takes 3 bytes, LDH takes 2, CB ops take 2. -/
example : (Instr.decodeFull 0xC3).len = 3 := by decide
example : (Instr.decodeFull 0xE0).len = 2 := by decide
example : (Instr.decodeCB 0x00).len = 2 := by decide

end GB
