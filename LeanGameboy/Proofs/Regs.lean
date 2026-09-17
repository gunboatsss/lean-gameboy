/-
  LeanGameboy.Proofs.Regs — AF register codec specifications.

  These pin the exact bit positions of the flag pack/unpack mapping
  definitionally. (Full pack-then-unpack roundtrips need BitVec
  shift-truncate theory for `hiByte`/`join16` and remain open;
  the flag directions avoid shifts entirely.)
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

end GB
