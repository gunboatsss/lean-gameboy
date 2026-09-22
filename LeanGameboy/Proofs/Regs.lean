/-
  LeanGameboy.Proofs.Regs — AF register codec specifications.

  These pin the exact bit positions of the flag pack/unpack mapping
  definitionally, plus exhaustive pack-then-unpack roundtrips below
  (the old BitVec shift-truncate gap is closed by finite enumeration:
  `join16` is fully characterized over all 65k byte pairs and `af` /
  `setAF` round-trips over all 4096 `(A, Z, N, H, C)` combos).
-/
import LeanGameboy.Cpu.Regs

namespace GB

/-- Unpacking restores A. -/
theorem setAF_a (r : Regs) (v : UInt16) : (r.setAF v).a = hiByte v := rfl

/-- Unpacking restores Z from bit 7. -/
theorem setAF_z (r : Regs) (v : UInt16) :
    (r.setAF v).z = bitGet (loByte v) 7 := rfl

/-- Unpacking restores N from bit 6. -/
theorem setAF_n (r : Regs) (v : UInt16) :
    (r.setAF v).n = bitGet (loByte v) 6 := rfl

/-- Unpacking restores H from bit 5. -/
theorem setAF_hf (r : Regs) (v : UInt16) :
    (r.setAF v).hf = bitGet (loByte v) 5 := rfl

/-- Unpacking restores C from bit 4. -/
theorem setAF_cf (r : Regs) (v : UInt16) :
    (r.setAF v).cf = bitGet (loByte v) 4 := rfl

/-- Pack anchor: DMG boot flags encode to 0x01B0. -/
example : Regs.bootDefaults.af = 0x01B0 := by decide

/-- Spot check: unpacking 0x01B0 restores A and the Z/H/C flags. -/
example : ((Regs.bootDefaults.setAF 0x01B0).a = 0x01) &&
    (Regs.bootDefaults.setAF 0x01B0).z &&
    !(Regs.bootDefaults.setAF 0x01B0).n &&
    (Regs.bootDefaults.setAF 0x01B0).hf &&
    (Regs.bootDefaults.setAF 0x01B0).cf := by decide

/-! ## Pack/unpack roundtrip (closes the open shift-truncate gap) -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Join then split restores both bytes (all 65k pairs, kernel `decide`). -/
theorem join16_roundtrip_all :
    ((List.range 256).all fun m =>
      (List.range 256).all fun n =>
        (hiByte (join16 (w8 m) (w8 n)) == w8 m) &&
        (loByte (join16 (w8 m) (w8 n)) == w8 n)) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Pack then unpack restores A and all four flags: all 256 values of A
    × all 16 flag combos (4096 cases, kernel `decide`). Other registers
    are preserved by construction (`setAF` only touches A/flags). -/
theorem af_roundtrip_all :
    ((List.range 256).all fun m =>
      [true, false].all fun z =>
        [true, false].all fun n =>
          [true, false].all fun h =>
            [true, false].all fun c =>
              let r : Regs := { a := w8 m, z := z, n := n, hf := h, cf := c }
              let r2 := r.setAF r.af
              (r2.a == r.a) && (r2.z == r.z) && (r2.n == r.n) &&
                (r2.hf == r.hf) && (r2.cf == r.cf)) = true := by
  decide

end GB
