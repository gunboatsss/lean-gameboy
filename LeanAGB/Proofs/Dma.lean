/-
  LeanAGB.Proofs.Dma — DMA data-movement contracts.

  `Proofs/Bus` pins cycle/regs/rom preservation per DMA primitive;
  here are the value semantics: overlap detection, window selection,
  the slow-path fallback condition, and closed copy instances
  (16-bit step, two-unit loop, bulk slice) plus the empty-loop law.
-/
import LeanAGB.Bus

namespace AGB

/-- Tiny EWRAM window for closed instances (blank framebuffer so
     `decide` never builds the 38400-pixel default). -/
def dmaTest : AGBState :=
  { ({} : AGBState) with
    ewram := ByteArray.mk #[0xEF, 0xBE, 0, 0, 0, 0], fb := #[] }

/-! ## Overlap detection -/

/-- Overlap is symmetric. -/
theorem rangesOverlap_symm (o1 o2 total : Nat) :
    rangesOverlap o1 o2 total = rangesOverlap o2 o1 total := by
  simp [rangesOverlap, Bool.and_comm]

/-- A nonempty range overlaps itself. -/
theorem rangesOverlap_self (o t : Nat) :
    rangesOverlap o o (t + 1) = true := by
  simp [rangesOverlap]

/-- Empty ranges never overlap. -/
theorem rangesOverlap_empty (o1 o2 : Nat) :
    rangesOverlap o1 o2 0 = false := by
  by_cases h1 : o1 < o2
  · have h2 : ¬ o2 < o1 := by omega
    simp [rangesOverlap, decide_eq_false h2]
  · simp [rangesOverlap, decide_eq_false h1]

/-! ## Window selection -/

/-- IO sources take the slow path. -/
theorem dmaLinSrc_io :
    dmaLinSrc dmaTest 0x04000000 4 = none := by
  decide

/-- Save addresses take the slow path as destinations. -/
theorem dmaLinDst_save : dmaLinDst 0x0E000000 4 = none := by
  decide

/-! ## Loop structure -/

/-- Empty fuel is the identity. -/
theorem dmaCopy_zero (s : AGBState) (src dst : UInt32) (is32 : Bool)
    (sstep dstep : Int) :
    dmaCopy s src dst 0 is32 sstep dstep = s := rfl

/-- A non-incrementing channel takes the exact slow loop. -/
theorem dmaRun_slow (s : AGBState) (src dst : UInt32) (count : Nat)
    (is32 : Bool) (sstep dstep : Int) (unit : Nat)
    (h : (sstep == (unit : Int)) = false) :
    dmaRun s src dst count is32 sstep dstep unit
      = dmaCopy s src dst count is32 sstep dstep := by
  have e : ¬ ((sstep == (unit : Int) && dstep == (unit : Int)) = true) := by
    simp [h]
  unfold dmaRun
  rw [ite_eq_right e]

/-! ## Closed copy instances (tiny EWRAM window, blank framebuffer
     so `decide` never builds the 38400-pixel default). -/

/-- One 16-bit unit lands byte-exact. -/
theorem dmaStep_16lew :
    memRead16 (dmaStep dmaTest 0x02000000 0x02000002 false) 0x02000002
      = 0xBEEF := by
  decide

/-- The copy source is preserved. -/
theorem dmaStep_preserves_src :
    memRead8 (dmaStep dmaTest 0x02000000 0x02000002 false) 0x02000000
      = 0xEF := by
  decide

/-- A two-unit incrementing loop chains through the written bytes. -/
theorem dmaCopy_two_units :
    memRead16 (dmaCopy dmaTest 0x02000000 0x02000002 2 false 2 2)
      0x02000004 = 0xBEEF := by
  decide

/-- Overlapping same-store windows fall back (no bulk). -/
theorem dmaBulk_overlap :
    dmaBulk dmaTest 0x02000000 0x02000002 4 = none := by
  decide

/-- Disjoint windows commit a byte-exact slice. -/
theorem dmaBulk_copies :
    ((dmaBulk dmaTest 0x02000000 0x02000004 2).getD dmaTest).ewram
      = ByteArray.mk #[0xEF, 0xBE, 0, 0, 0xEF, 0xBE] := by
  decide

end AGB
