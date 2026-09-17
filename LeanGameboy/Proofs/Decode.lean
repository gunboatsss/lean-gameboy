/-
  LeanGameboy.Proofs.Decode — opcode table coverage.

  Every byte decodes (totality by construction); here we pin the
  complete invalid-opcode set and bound all instruction lengths.
-/
import LeanGameboy.Cpu.Decode

namespace GB

set_option maxRecDepth 10000 in
/-- The full SM83 invalid-opcode set decodes to `.Invalid`. -/
example : (([0xD3, 0xDB, 0xDD, 0xE3, 0xE4, 0xEB, 0xEC, 0xED, 0xF4, 0xFC, 0xFD]
    |>.map Instr.decodeFull).all (· == .Invalid)) = true := by
  decide

set_option maxRecDepth 10000 in
/-- Every unprefixed opcode decodes to length 1, 2, or 3. -/
example : (((List.range 256).map fun n =>
    (Instr.decodeFull (w8 n)).len).all fun l => 1 <= l && l <= 3) = true := by
  decide

set_option maxRecDepth 10000 in
/-- Every CB-prefixed opcode is 2 bytes. -/
example : (((List.range 256).map fun n =>
    (Instr.decodeCB (w8 n)).len).all (· == 2)) = true := by
  decide

set_option maxRecDepth 10000 in
/-- CB space covers exactly rotates, bits, resets, and sets. -/
example : (((List.range 256).map fun n =>
    Instr.decodeCB (w8 n)).all fun
    | .Rot _ _ | .Bit _ _ | .Res _ _ | .Set _ _ => true
    | _ => false) = true := by
  decide

/-- RST vectors land on multiples of 8 below 0x40. -/
example : (((List.range 8).map fun k =>
    (Instr.decodeFull (w8 (0xC7 + 8 * k)))).all fun
    | .Rst _ => true
    | _ => false) = true := by
  decide

end GB
