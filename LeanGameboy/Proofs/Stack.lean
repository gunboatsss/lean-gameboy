/-
  LeanGameboy.Proofs.Stack — HRAM read-after-write and the push/pop roundtrip.

  Closes the open item in `Proofs/Halt.lean`: the inhibited address pushed
  by double-`HALT` + IRQ dispatch is provably retrieved
  (`serviceIrq_pushes_pc`). `ByteArray` reasoning goes through
  `Array.getElem_setIfInBounds` via the `data` projection; `UInt16`
  index arithmetic via `UInt16.toNat_add`.
-/
import LeanGameboy.Bus
import LeanGameboy.Proofs.Bus
import Std.Tactic.BVDecide

namespace GB

/-! ## ByteArray read-after-write -/

/-- Writes preserve the size. -/
theorem bset_size (b : ByteArray) (i : Nat) (v : UInt8) :
    (bset b i v).size = b.size := by
  unfold bset
  split
  · simp only [ByteArray.set!]
    show (b.data.setIfInBounds i v).size = b.data.size
    exact Array.size_setIfInBounds ..
  · rfl

/-- Reading back the written byte. -/
theorem bget_bset_same (b : ByteArray) (i : Nat) (v : UInt8) (hi : i < b.size) :
    bget (bset b i v) i = v := by
  have hsize : (b.set! i v).size = b.size := by
    simp only [ByteArray.set!]
    show (b.data.setIfInBounds i v).size = b.data.size
    exact Array.size_setIfInBounds ..
  have hdi : i < b.data.size := hi
  have h2 := Array.getElem_setIfInBounds (xs := b.data) (i := i) (a := v) (j := i) hdi
  simp only [ite_true] at h2
  unfold bset bget
  simp only [hi, hsize, ite_true]
  exact h2

/-- Writes never clobber another address. -/
theorem bget_bset_ne (b : ByteArray) (i j : Nat) (v : UInt8)
    (hi : i < b.size) (hj : j < b.size) (hne : i ≠ j) :
    bget (bset b i v) j = bget b j := by
  have hsize : (b.set! i v).size = b.size := by
    simp only [ByteArray.set!]
    show (b.data.setIfInBounds i v).size = b.data.size
    exact Array.size_setIfInBounds ..
  have hdi : j < b.data.size := hj
  have h2 := Array.getElem_setIfInBounds (xs := b.data) (i := i) (a := v) (j := j) hdi
  simp only [hne, ite_false] at h2
  unfold bset bget
  simp only [hi, hj, hsize, ite_true]
  exact h2

/-! ## HRAM bus roundtrip -/

-- Deep `ByteArray` unfolding (`set!`/`get` via `data`) needs headroom.
set_option maxRecDepth 100000

/-- The eight cascade guards for an HRAM address, in one package. -/
theorem hram_addr_guards (a : UInt16)
    (hlo : 0xFF80 ≤ a.toNat) (hhi : a.toNat < 0xFFFF) :
    ¬ a.toNat < 0x8000 ∧ ¬ a.toNat < 0xA000 ∧ ¬ a.toNat < 0xC000 ∧
    ¬ a.toNat < 0xE000 ∧ ¬ a.toNat < 0xFE00 ∧ ¬ a.toNat < 0xFEA0 ∧
    ¬ a.toNat < 0xFF00 ∧ ¬ a.toNat < 0xFF80 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- An HRAM write lands exactly in `hram` (nothing else moves). -/
theorem busWrite_hram_eq (s : GBState) (a : UInt16) (v : UInt8)
    (hlo : 0xFF80 ≤ a.toNat) (hhi : a.toNat < 0xFFFF) :
    (busWrite s a v).1 =
      { s with hram := bset s.hram (a.toNat - 0xFF80) v } := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := hram_addr_guards a hlo hhi
  simp only [busWrite, e1, e2, e3, e4, e5, e6, e7, e8, hhi, ite_true, ite_false]

/-- HRAM writes preserve registers. -/
theorem busWrite_hram_regs (s : GBState) (a : UInt16) (v : UInt8)
    (hlo : 0xFF80 ≤ a.toNat) (hhi : a.toNat < 0xFFFF) :
    (busWrite s a v).1.regs = s.regs := by
  rw [busWrite_hram_eq s a v hlo hhi]

/-- HRAM writes preserve the size. -/
theorem busWrite_hram_size (s : GBState) (a : UInt16) (v : UInt8)
    (hlo : 0xFF80 ≤ a.toNat) (hhi : a.toNat < 0xFFFF) :
    (busWrite s a v).1.hram.size = s.hram.size := by
  rw [busWrite_hram_eq s a v hlo hhi]
  exact bset_size ..

set_option maxRecDepth 100000 in
/-- Reading back an HRAM write. -/
theorem hram_rw (s : GBState) (a : UInt16) (v : UInt8)
    (hlo : 0xFF80 ≤ a.toNat) (hhi : a.toNat < 0xFFFF)
    (hsize : s.hram.size = 0x7F) :
    busRead (busWrite s a v).1 a = v := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := hram_addr_guards a hlo hhi
  have hb : a.toNat - 0xFF80 < s.hram.size := by omega
  rw [busWrite_hram_eq s a v hlo hhi]
  simp only [busRead, e1, e2, e3, e4, e5, e6, e7, e8, hhi, ite_true, ite_false]
  exact bget_bset_same _ _ _ hb

set_option maxRecDepth 100000 in
/-- An HRAM write never clobbers another HRAM address. -/
theorem hram_rw_ne (s : GBState) (i j : UInt16) (w : UInt8)
    (hilo : 0xFF80 ≤ i.toNat) (hihi : i.toNat < 0xFFFF)
    (hjlo : 0xFF80 ≤ j.toNat) (hjhi : j.toNat < 0xFFFF)
    (hsize : s.hram.size = 0x7F) (hne : i.toNat ≠ j.toNat) :
    busRead (busWrite s j w).1 i = busRead s i := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := hram_addr_guards i hilo hihi
  -- NOTE: `omega` recurses badly on hypotheses containing truncated `Nat`
  -- subtraction in this toolchain, so prove the index bounds first (their
  -- proofs see no such hypotheses) and `clear` the subtraction hyps
  -- wherever they are not needed (each `have`-block has its own context).
  have hbij : i.toNat - 0xFF80 < (bset s.hram (j.toNat - 0xFF80) w).size := by
    rw [bset_size]; omega
  have hbj : j.toNat - 0xFF80 < s.hram.size := by clear hbij; omega
  have hbi : i.toNat - 0xFF80 < s.hram.size := by clear hbij hbj; omega
  have hne' : i.toNat - 0xFF80 ≠ j.toNat - 0xFF80 := by clear hbij hbj hbi; omega
  rw [busWrite_hram_eq s j w hjlo hjhi]
  simp only [busRead, e1, e2, e3, e4, e5, e6, e7, e8, hihi, ite_true, ite_false]
  exact bget_bset_ne _ _ _ _ hbj hbi (Ne.symm hne')

/-! ## 16-bit and push/pop roundtrips -/

/-- Splitting a word and rejoining is the identity. -/
theorem join_split (v : UInt16) : join16 (hiByte v) (loByte v) = v := by
  simp only [hiByte, loByte, join16]
  bv_decide

/-- A 16-bit write followed by a read retrieves the value (both bytes
    in HRAM; `hsp` rules out wraparound so `sp' + 1` is exact). -/
theorem write16_read16_hram (s : GBState) (sp' : UInt16) (v : UInt16)
    (hlo : 0xFF80 ≤ sp'.toNat) (hsp : sp'.toNat + 1 < 0xFFFF)
    (hsize : s.hram.size = 0x7F) :
    read16 (write16 s sp' v).1 sp' = v := by
  have hlt : sp'.toNat + 1 < 65536 := by omega
  have hplus : (sp' + 1).toNat = sp'.toNat + 1 := by
    have hta := UInt16.toNat_add sp' 1
    have h6 : (2 : Nat) ^ 16 = 65536 := by decide
    rw [hta, h6]
    exact Nat.mod_eq_of_lt hlt
  have hsp1lo : 0xFF80 ≤ (sp' + 1).toNat := by omega
  have hsp1hi : (sp' + 1).toNat < 0xFFFF := by omega
  have hhi' : sp'.toNat < 0xFFFF := by omega
  have hne : sp'.toNat ≠ (sp' + 1).toNat := by omega
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := hram_addr_guards sp' hlo hhi'
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ :=
    hram_addr_guards (sp' + 1) hsp1lo hsp1hi
  simp only [write16, read16, busWrite, busRead,
    e1, e2, e3, e4, e5, e6, e7, e8, hhi',
    f1, f2, f3, f4, f5, f6, f7, f8, hsp1hi,
    ite_true, ite_false]
  have hbij : (sp' + 1).toNat - 0xFF80
      < (bset s.hram (sp'.toNat - 0xFF80) (loByte v)).size := by
    rw [bset_size]; omega
  have hbi : sp'.toNat - 0xFF80 < s.hram.size := by clear hbij; omega
  have hbi2 : sp'.toNat - 0xFF80
      < (bset s.hram (sp'.toNat - 0xFF80) (loByte v)).size := by
    rw [bset_size]; clear hbij hbi; omega
  have hne' : sp'.toNat - 0xFF80 ≠ (sp' + 1).toNat - 0xFF80 := by
    clear hbij hbi hbi2; omega
  have hHi : bget
      (bset (bset s.hram (sp'.toNat - 0xFF80) (loByte v))
        ((sp' + 1).toNat - 0xFF80) (hiByte v)) ((sp' + 1).toNat - 0xFF80)
      = hiByte v :=
    bget_bset_same _ _ _ hbij
  have hLo : bget
      (bset (bset s.hram (sp'.toNat - 0xFF80) (loByte v))
        ((sp' + 1).toNat - 0xFF80) (hiByte v)) (sp'.toNat - 0xFF80)
      = loByte v :=
    calc _ = bget (bset s.hram (sp'.toNat - 0xFF80) (loByte v))
              (sp'.toNat - 0xFF80) :=
          bget_bset_ne _ _ _ _ hbij hbi2 (Ne.symm hne')
      _ = loByte v := bget_bset_same _ _ _ hbi
  rw [hHi, hLo]
  exact join_split v

/-! ## Push/pop roundtrip -/

/-- Popping after pushing retrieves the value (stack in HRAM). -/
theorem push_pop_hram (s : GBState) (v : UInt16)
    (hlo : 0xFF80 ≤ (s.regs.sp - 2).toNat)
    (hsp : (s.regs.sp - 2).toNat + 1 < 0xFFFF)
    (hsize : s.hram.size = 0x7F) :
    (pop (push s v).1).2 = v := by
  have hlt : (s.regs.sp - 2).toNat + 1 < 65536 := by omega
  have hplus : ((s.regs.sp - 2) + 1).toNat = (s.regs.sp - 2).toNat + 1 := by
    have hta := UInt16.toNat_add (s.regs.sp - 2) 1
    have h6 : (2 : Nat) ^ 16 = 65536 := by decide
    rw [hta, h6]
    exact Nat.mod_eq_of_lt hlt
  have hsp1lo : 0xFF80 ≤ ((s.regs.sp - 2) + 1).toNat := by omega
  have hsp1hi : ((s.regs.sp - 2) + 1).toNat < 0xFFFF := by omega
  have hhi' : (s.regs.sp - 2).toNat < 0xFFFF := by omega
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ :=
    hram_addr_guards (s.regs.sp - 2) hlo hhi'
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ :=
    hram_addr_guards ((s.regs.sp - 2) + 1) hsp1lo hsp1hi
  simp only [push, pop, write16, read16, busWrite, busRead,
    e1, e2, e3, e4, e5, e6, e7, e8, hhi',
    f1, f2, f3, f4, f5, f6, f7, f8, hsp1hi,
    ite_true, ite_false]
  have hne : (s.regs.sp - 2).toNat ≠ ((s.regs.sp - 2) + 1).toNat := by omega
  have hbij : ((s.regs.sp - 2) + 1).toNat - 0xFF80
      < (bset s.hram ((s.regs.sp - 2).toNat - 0xFF80) (loByte v)).size := by
    rw [bset_size]; omega
  have hbi : (s.regs.sp - 2).toNat - 0xFF80 < s.hram.size := by
    clear hbij; omega
  have hbi2 : (s.regs.sp - 2).toNat - 0xFF80
      < (bset s.hram ((s.regs.sp - 2).toNat - 0xFF80) (loByte v)).size := by
    rw [bset_size]; clear hbij hbi; omega
  have hne' : (s.regs.sp - 2).toNat - 0xFF80
      ≠ ((s.regs.sp - 2) + 1).toNat - 0xFF80 := by
    clear hbij hbi hbi2; omega
  have hHi : bget
      (bset (bset s.hram ((s.regs.sp - 2).toNat - 0xFF80) (loByte v))
        (((s.regs.sp - 2) + 1).toNat - 0xFF80) (hiByte v))
        (((s.regs.sp - 2) + 1).toNat - 0xFF80)
      = hiByte v :=
    bget_bset_same _ _ _ hbij
  have hLo : bget
      (bset (bset s.hram ((s.regs.sp - 2).toNat - 0xFF80) (loByte v))
        (((s.regs.sp - 2) + 1).toNat - 0xFF80) (hiByte v))
        ((s.regs.sp - 2).toNat - 0xFF80)
      = loByte v :=
    calc _ = bget (bset s.hram ((s.regs.sp - 2).toNat - 0xFF80) (loByte v))
              ((s.regs.sp - 2).toNat - 0xFF80) :=
          bget_bset_ne _ _ _ _ hbij hbi2 (Ne.symm hne')
      _ = loByte v := bget_bset_same _ _ _ hbi
  rw [hHi, hLo]
  exact join_split v

/-! ## Advance preservation and the inhibited address -/

/-- Push projections through `ite` (the `snd_ite` pattern for state). -/
theorem proj_ite_sp (c : Prop) [Decidable c] (a b : GBState) :
    (if c then a else b).regs.sp = if c then a.regs.sp else b.regs.sp := by
  by_cases h : c <;> simp [h]

theorem proj_ite_hram (c : Prop) [Decidable c] (a b : GBState) :
    (if c then a else b).hram = if c then a.hram else b.hram := by
  by_cases h : c <;> simp [h]

/-- `advance` never moves the stack pointer. -/
theorem advance_sp (s : GBState) (m : Nat) : (advance s m).regs.sp = s.regs.sp := by
  simp only [advance, proj_ite_sp, finishLine_sp]
  first | rfl | (split <;> first | rfl | (split <;> rfl))

/-- `advance` never touches HRAM. -/
theorem advance_hram (s : GBState) (m : Nat) : (advance s m).hram = s.hram := by
  simp only [advance, proj_ite_hram, finishLine_hram]
  first | rfl | (split <;> first | rfl | (split <;> rfl))

/-! ## IRQ dispatch pushes the inhibited address -/

/-- Servicing an interrupt pushes the *current* PC — under the halt bug
    (`Halt.halt_spin`, `halt_arms`) that PC is the frozen/un-incremented
    one, i.e. the `double-halt-cancel` inhibited return address. -/
theorem serviceIrq_pushes_pc (s : GBState) (b : Nat)
    (hlo : 0xFF80 ≤ (s.regs.sp - 2).toNat)
    (hsp : (s.regs.sp - 2).toNat + 1 < 0xFFFF)
    (hsize : s.hram.size = 0x7F) :
    read16 (serviceIrq s b) (serviceIrq s b).regs.sp = s.regs.pc := by
  have hlt : (s.regs.sp - 2).toNat + 1 < 65536 := by omega
  have hplus : ((s.regs.sp - 2) + 1).toNat = (s.regs.sp - 2).toNat + 1 := by
    have hta := UInt16.toNat_add (s.regs.sp - 2) 1
    have h6 : (2 : Nat) ^ 16 = 65536 := by decide
    rw [hta, h6]
    exact Nat.mod_eq_of_lt hlt
  have hsp1lo : 0xFF80 ≤ ((s.regs.sp - 2) + 1).toNat := by omega
  have hsp1hi : ((s.regs.sp - 2) + 1).toNat < 0xFFFF := by omega
  have hhi' : (s.regs.sp - 2).toNat < 0xFFFF := by omega
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ :=
    hram_addr_guards (s.regs.sp - 2) hlo hhi'
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ :=
    hram_addr_guards ((s.regs.sp - 2) + 1) hsp1lo hsp1hi
  simp only [serviceIrq, push, write16, read16, busWrite, busRead,
    advance_sp, advance_hram,
    e1, e2, e3, e4, e5, e6, e7, e8, hhi',
    f1, f2, f3, f4, f5, f6, f7, f8, hsp1hi,
    ite_true, ite_false]
  have hne : (s.regs.sp - 2).toNat ≠ ((s.regs.sp - 2) + 1).toNat := by omega
  have hbij : ((s.regs.sp - 2) + 1).toNat - 0xFF80
      < (bset s.hram ((s.regs.sp - 2).toNat - 0xFF80) (loByte s.regs.pc)).size := by
    rw [bset_size]; omega
  have hbi : (s.regs.sp - 2).toNat - 0xFF80 < s.hram.size := by
    clear hbij; omega
  have hbi2 : (s.regs.sp - 2).toNat - 0xFF80
      < (bset s.hram ((s.regs.sp - 2).toNat - 0xFF80) (loByte s.regs.pc)).size := by
    rw [bset_size]; clear hbij hbi; omega
  have hne' : (s.regs.sp - 2).toNat - 0xFF80
      ≠ ((s.regs.sp - 2) + 1).toNat - 0xFF80 := by
    clear hbij hbi hbi2; omega
  have hHi : bget
      (bset (bset s.hram ((s.regs.sp - 2).toNat - 0xFF80) (loByte s.regs.pc))
        (((s.regs.sp - 2) + 1).toNat - 0xFF80) (hiByte s.regs.pc))
        (((s.regs.sp - 2) + 1).toNat - 0xFF80)
      = hiByte s.regs.pc :=
    bget_bset_same _ _ _ hbij
  have hLo : bget
      (bset (bset s.hram ((s.regs.sp - 2).toNat - 0xFF80) (loByte s.regs.pc))
        (((s.regs.sp - 2) + 1).toNat - 0xFF80) (hiByte s.regs.pc))
        ((s.regs.sp - 2).toNat - 0xFF80)
      = loByte s.regs.pc :=
    calc _ = bget (bset s.hram ((s.regs.sp - 2).toNat - 0xFF80) (loByte s.regs.pc))
              ((s.regs.sp - 2).toNat - 0xFF80) :=
          bget_bset_ne _ _ _ _ hbij hbi2 (Ne.symm hne')
      _ = loByte s.regs.pc := bget_bset_same _ _ _ hbi
  rw [hHi, hLo]
  exact join_split s.regs.pc

/-- The `RST` instruction pushes its (possibly bug-adjusted) return
    address: with the halt bug armed this is `pc + len - 1`, matching
    `Halt.bugged_nextpc`. -/
theorem exec_rst_pushes (s : GBState) (k : Nat) (pc : UInt16)
    (hlo : 0xFF80 ≤ (s.regs.sp - 2).toNat)
    (hsp : (s.regs.sp - 2).toNat + 1 < 0xFFFF)
    (hsize : s.hram.size = 0x7F) :
    read16 (exec s (.Rst k) pc).1 ((exec s (.Rst k) pc).1.regs.sp)
      = pc + w16 (Instr.len (.Rst k)) - (if s.haltBug then 1 else 0) := by
  have hlt : (s.regs.sp - 2).toNat + 1 < 65536 := by omega
  have hplus : ((s.regs.sp - 2) + 1).toNat = (s.regs.sp - 2).toNat + 1 := by
    have hta := UInt16.toNat_add (s.regs.sp - 2) 1
    have h6 : (2 : Nat) ^ 16 = 65536 := by decide
    rw [hta, h6]
    exact Nat.mod_eq_of_lt hlt
  have hsp1lo : 0xFF80 ≤ ((s.regs.sp - 2) + 1).toNat := by omega
  have hsp1hi : ((s.regs.sp - 2) + 1).toNat < 0xFFFF := by omega
  have hhi' : (s.regs.sp - 2).toNat < 0xFFFF := by omega
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ :=
    hram_addr_guards (s.regs.sp - 2) hlo hhi'
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ :=
    hram_addr_guards ((s.regs.sp - 2) + 1) hsp1lo hsp1hi
  simp only [exec, push, write16, read16, busWrite, busRead,
    e1, e2, e3, e4, e5, e6, e7, e8, hhi',
    f1, f2, f3, f4, f5, f6, f7, f8, hsp1hi,
    ite_true, ite_false]
  have hne : (s.regs.sp - 2).toNat ≠ ((s.regs.sp - 2) + 1).toNat := by omega
  have hbij : ((s.regs.sp - 2) + 1).toNat - 0xFF80
      < (bset s.hram ((s.regs.sp - 2).toNat - 0xFF80)
          (loByte (pc + w16 (Instr.Rst k).len - if s.haltBug = true then 1 else 0))).size := by
    rw [bset_size]; omega
  have hbi : (s.regs.sp - 2).toNat - 0xFF80 < s.hram.size := by
    clear hbij; omega
  have hbi2 : (s.regs.sp - 2).toNat - 0xFF80
      < (bset s.hram ((s.regs.sp - 2).toNat - 0xFF80)
          (loByte (pc + w16 (Instr.Rst k).len - if s.haltBug = true then 1 else 0))).size := by
    rw [bset_size]; clear hbij hbi; omega
  have hne' : (s.regs.sp - 2).toNat - 0xFF80
      ≠ ((s.regs.sp - 2) + 1).toNat - 0xFF80 := by
    clear hbij hbi hbi2; omega
  have hHi : bget
      (bset (bset s.hram ((s.regs.sp - 2).toNat - 0xFF80)
          (loByte (pc + w16 (Instr.Rst k).len - if s.haltBug = true then 1 else 0)))
        (((s.regs.sp - 2) + 1).toNat - 0xFF80)
        (hiByte (pc + w16 (Instr.Rst k).len - if s.haltBug = true then 1 else 0)))
        (((s.regs.sp - 2) + 1).toNat - 0xFF80)
      = hiByte (pc + w16 (Instr.Rst k).len - if s.haltBug = true then 1 else 0) :=
    bget_bset_same _ _ _ hbij
  have hLo : bget
      (bset (bset s.hram ((s.regs.sp - 2).toNat - 0xFF80)
          (loByte (pc + w16 (Instr.Rst k).len - if s.haltBug = true then 1 else 0)))
        (((s.regs.sp - 2) + 1).toNat - 0xFF80)
        (hiByte (pc + w16 (Instr.Rst k).len - if s.haltBug = true then 1 else 0)))
        ((s.regs.sp - 2).toNat - 0xFF80)
      = loByte (pc + w16 (Instr.Rst k).len - if s.haltBug = true then 1 else 0) :=
    calc _ = bget (bset s.hram ((s.regs.sp - 2).toNat - 0xFF80)
              (loByte (pc + w16 (Instr.Rst k).len - if s.haltBug = true then 1 else 0)))
              ((s.regs.sp - 2).toNat - 0xFF80) :=
          bget_bset_ne _ _ _ _ hbij hbi2 (Ne.symm hne')
      _ = loByte (pc + w16 (Instr.Rst k).len - if s.haltBug = true then 1 else 0) :=
          bget_bset_same _ _ _ hbi
  rw [hHi, hLo]
  exact join_split _

end GB
