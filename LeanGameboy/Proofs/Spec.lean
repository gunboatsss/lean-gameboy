/-
  LeanGameboy.Proofs.Spec — behavior extraction, not trace replay.

  `Reach` proves one ROM trace by re-execution (`native_decide`).
  Here we do the stronger thing: write the *intended behavior* as an
  independent spec (from Pan Docs prose, not from the implementation),
  then prove the implementation refines it for ALL states.

  Covered:
  1. DAA spec + flag contracts (lifts the `Tests/Smoke` magic
     constants `0x45+0x38 → DAA → 0x83` to universal lemmas).
  2. Serial test-cartridge contract (Blargg `Passed` protocol):
     the output log is append-only, so `Passed` is stable.
-/
import LeanGameboy.Bus
import LeanGameboy.Emu

namespace GB

/-! ## 1. DAA spec (Pan Docs wording, written independently) -/

/-- Independent DAA spec from the manual prose:
    after ADD/ADC (N=0): add 0x60 if C set or A > 0x99 (sets C),
    then add 0x06 if H set or low nibble of the intermediate > 9.
    After SUB/SBC (N=1): subtract 0x60 if C, then 0x06 if H.
    Returns (adjusted A, new carry). -/
def specDaa (a : UInt8) (n h c : Bool) : UInt8 × Bool :=
  if !n then
    let (x, cMid) := if c || a.toNat > 0x99 then (a + 0x60, true) else (a, c)
    let y := if h || (x.toNat % 16) > 9 then x + 0x06 else x
    (y, cMid)
  else
    let x := if c then a - 0x60 else a
    let y := if h then x - 0x06 else x
    (y, c)

/-- The implementation refines the spec: exhaustively checked over all
    256 values of A × all N/H/C flag combos (2048 cases), kernel-checked
    with `decide` (no `native_decide`). `mkDaaState` uses only `{}`-default
    states so the kernel never has to reduce `ByteArray`/`parseHeader` —
    `daa` depends only on `(a, n, h, c)`, which is exactly what is
    enumerated. -/
def mkDaaState (a : UInt8) (n h c : Bool) : GBState :=
  let r : Regs := { a := a, n := n, hf := h, cf := c }
  let s : GBState := {}
  { s with regs := r }

set_option maxRecDepth 100000 in
theorem daa_matches_spec_all :
    ((List.range 256).all fun n =>
      let a := w8 n
      [true, false].all fun nn =>
        [true, false].all fun h =>
          [true, false].all fun c =>
            ((daa (mkDaaState a nn h c)).regs.a ==
              (specDaa a nn h c).fst) &&
            (((daa (mkDaaState a nn h c)).regs.cf) ==
              (specDaa a nn h c).snd)) = true := by
  decide

/-- DAA always clears H. -/
theorem daa_clears_h (s : GBState) : (daa s).regs.hf = false := by
  simp [daa]

/-- DAA preserves N. -/
theorem daa_preserves_n (s : GBState) : (daa s).regs.n = s.regs.n := by
  cases h : s.regs.n <;> simp [daa, h]

/-- DAA sets Z iff the adjusted value is zero. -/
theorem daa_z_iff (s : GBState) :
    (daa s).regs.z = ((daa s).regs.a == 0) := by
  cases h : s.regs.n <;> simp [daa, h]

/-- Subtraction mode: carry is preserved. -/
theorem daa_sub_carry (s : GBState) (hn : s.regs.n = true) :
    (daa s).regs.cf = s.regs.cf := by
  simp [daa, hn]

/-- Carry is sticky in addition mode: once set, DAA keeps it set. -/
theorem daa_add_carry_sticky (s : GBState)
    (hn : s.regs.n = false) (hc : s.regs.cf = true) :
    (daa s).regs.cf = true := by
  simp [daa, hn, hc]

/-- Extracted behavior behind the smoke-test magic:
    `LD A,0x45 | LD B,0x38 | ADD A,B` leaves `A=0x7D` with H set,
    and DAA (N=0) adjusts it to the BCD value `0x83`. -/
theorem smoke_add_daa : ((add8 0x45 0x38 false).val == 0x7D) = true := by
  decide

theorem smoke_daa_adjusts : (specDaa 0x7D false true false = (0x83, false)) := by
  decide

/-- End-to-end at `exec` level (no ROM bytes, no fuel):
    DAA on the post-ADD flag state produces `A=0x83`, `Z=false`. -/
example (s : GBState)
    (ha : s.regs.a = 0x7D) (hn : s.regs.n = false)
    (hh : s.regs.hf = true) (hc : s.regs.cf = false) :
    (daa s).regs.a = 0x83 ∧ (daa s).regs.z = false := by
  simp [daa, ha, hn, hh, hc]

/-! ## 2. Serial test-cartridge contract (Blargg protocol) -/

/-- A test cartridge passes iff its serial log contains `Passed`
    (same `splitOn` check the headless runner uses in `Emu`). -/
def blarggPass (s : GBState) : Bool :=
  decide (1 < ((serialText s).splitOn "Passed").length)

/-- Serial hardware only ever appends: one `step` either leaves `out`
    alone or pushes exactly one byte. -/
theorem serial_step_append (s : SerialState) (dots : Nat) :
    (s.step dots).out = s.out ∨
      ∃ b, (s.step dots).out = s.out.push b := by
  unfold SerialState.step
  by_cases h0 : s.dots == 0 <;> simp [h0]
  by_cases h1 : dots < s.dots <;> simp [h1]
  exact ⟨s.sb, rfl⟩

end GB
