/-
  LeanGameboy.Proofs.Reach — bounded reachability, machine-checked.

  This is the furthest the "prove a playthrough" idea goes: for a
  FIXED input trace of length N, we can prove the reached state by
  evaluating the emulator — but only with `native_decide` (compile
  the checker to native code). Kernel `decide`/`rfl` cannot do this:
  checking = re-execution, and the kernel reduces heavy `GBState`
  terms ~100-1000x slower than compiled code.

  Scaling walls for a full-game proof (e.g. a Pokémon champion run):
  1. Kernel wall: ~10^10 instructions × kernel slowdown = millennia.
  2. ROM-as-term: `native_decide` still needs the ROM as a closed
     term; elaborating a 1MB literal (Pokémon Red) chokes the
     elaborator before checking starts. Only tiny synthetic ROMs fit.
  3. Trace search: verification needs the WINNING input trace first —
     a full-game TAS is its own unsolved search problem.

  What remains provable: universal (∀) properties (the rest of this
  directory) plus bounded (∃-trace-of-length-N) reachability like below.
-/
import LeanGameboy.Emu

namespace GB

/-- Synthetic nested-loop ROM (~132k instructions):
    B counts via fresh `INC B` flags after each inner run, so the
    outer loop truly iterates 256 times; on exit B == 0, stored to
    0xC000 with marker 0x42 at 0xC001. -/
def reachROM : ByteArray :=
  let blank := ByteArray.mk (Array.mk (List.replicate 0x8000 0))
  let poke (b : ByteArray) (base : Nat) (xs : List Nat) : ByteArray :=
    xs.foldl (fun (acc : ByteArray × Nat) v =>
      (bset acc.1 acc.2 (w8 v), acc.2 + 1)) (b, base) |>.1
  poke blank 0x0100
    [0x06, 0x00,       -- LD B,0
     0x0E, 0x00,       -- outer: LD C,0
     0x0C,             -- inner: INC C
     0x20, 0xFD,       -- JR NZ,-3 (to inner)
     0x04,             -- INC B (fresh flags for outer check)
     0x20, 0xF8,       -- JR NZ,-8 (to outer)
     0x78,             -- LD A,B (== 0 on exit)
     0xEA, 0x00, 0xC0, -- LD (0xC000),A
     0x3E, 0x42,       -- LD A,0x42
     0xEA, 0x01, 0xC0, -- LD (0xC001),A
     0x18, 0xFE]       -- loop: JR -2

/-- 256·(2 + 256·2 + 1) + setup/tail ≈ 131850 instructions. -/
def reachFuel : Nat := 140000

/-- Bounded reachability: the scripted run stores B == 0 and the
    marker. Checked by native compilation (`decide` in the kernel
    would need ~10^8 reductions for this trace). -/
example : (busRead (runInstrs (loadROM reachROM) reachFuel) 0xC000 == 0) &&
    (busRead (runInstrs (loadROM reachROM) reachFuel) 0xC001 == 0x42) &&
    ((runInstrs (loadROM reachROM) reachFuel).regs.b == 0) := by
  native_decide

end GB
