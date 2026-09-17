/-
  gb-test — end-to-end smoke test with a hand-assembled synthetic ROM.

  Program (loaded at 0x0100):
      LD A,0x45 | LD B,0x38 | ADD A,B | DAA | LD (0xC001),A
      LD A,0x42 | LD B,0x10 | ADD A,B | LD (0xC000),A
      loop: JR loop
  Expected: [0xC001] = 0x83 (BCD of 45+38), [0xC000] = 0x52,
  plus one full frame advances PPU frame counter and VBlank fires.
-/
import LeanGameboy

open GB

/-- Assemble the synthetic test ROM (32 KiB, NoMBC header). -/
def testROM : ByteArray :=
  let blank := ByteArray.mk (Array.mk (List.replicate 0x8000 0))
  let poke (b : ByteArray) (base : Nat) (xs : List Nat) : ByteArray :=
    xs.foldl (fun (acc : ByteArray × Nat) v =>
      (bset acc.1 acc.2 (w8 v), acc.2 + 1)) (b, base) |>.1
  let code : List Nat :=
    [0x3E, 0x45,       -- LD A,0x45
     0x06, 0x38,       -- LD B,0x38
     0x80,             -- ADD A,B      (0x45+0x38 = 0x7D, H=1)
     0x27,             -- DAA          (→ 0x83)
     0xEA, 0x01, 0xC0, -- LD (0xC001),A
     0x3E, 0x42,       -- LD A,0x42
     0x06, 0x10,       -- LD B,0x10
     0x80,             -- ADD A,B      (→ 0x52)
     0xEA, 0x00, 0xC0, -- LD (0xC000),A
     0x18, 0xFE]       -- loop: JR -2
  let b1 := poke blank 0x0100 code
  -- minimal header: ROM-only, 32 KiB, no RAM
  let b2 := poke b1 0x0147 [0x00, 0x00, 0x00]
  b2

def check (name : String) (cond : Bool) : IO Bool := do
  IO.println s!"[test] {name}: {if cond then "PASS" else "FAIL"}"
  pure cond

def main : IO Unit := do
  let s0 := loadROM testROM
  let s1 := runInstrs s0 9
  let m0 := busRead s1 0xC000
  let m1 := busRead s1 0xC001
  let mut ok := true
  let c1 ← check "ADD result [0xC000] == 0x52" (m0 == 0x52)
  ok := c1 && ok
  let c2 ← check "DAA result [0xC001] == 0x83" (m1 == 0x83)
  ok := c2 && ok
  let c3 ← check "PC spins in JR loop" (s1.regs.pc == 0x0111)
  ok := c3 && ok
  -- one frame: PPU wraps, VBlank requested, serial quiet
  let s2 := runFrame s1
  let c4 ← check "frame advanced" (s2.ppu.frame == s1.ppu.frame + 1)
  ok := c4 && ok
  let c5 ← check "VBlank interrupt fired" (bitGet s2.if_ 0)
  ok := c5 && ok
  let c6 ← check "cycles look sane (>17000 M-cycles)" (s2.cycles > 17000)
  ok := c6 && ok
  -- DAA flag state right after the DAA instruction (instr #4)
  let s3 := runInstrs s0 4
  let c7 ← check "DAA sets A=0x83 Z=0" (s3.regs.a == 0x83 && !s3.regs.z)
  ok := c7 && ok
  -- bulk timer: 100 M-cycles at 262144 Hz (bit 3) = 400/16 = 25 TIMA ticks
  let t1 := TimerState.step { tac := 0x05 } 100
  let c8 ← check "timer TIMA counts 25" (t1.tima == 25)
  ok := c8 && ok
  let c9 ← check "timer DIV = 400/256 = 1" (t1.div == 1)
  ok := c9 && ok
  -- timer overflow reloads TMA and raises IRQ
  let t2 := TimerState.step { tac := 0x05, tima := 0xFF, tma := 0x33 } 100
  let c10 ← check "timer overflow → TMA reload + IRQ" (t2.tima == 0x4B && t2.irq)
  ok := c10 && ok
  if ok then IO.println "[test] ALL PASS" else IO.Process.exit 1
