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
  -- dots-based timer step matches M-cycle step at single speed
  let t3 := TimerState.stepDots { tac := 0x05 } 400
  let c11 ← check "timer stepDots(400) == step(100)" (t3.tima == 25 && t3.div == 1)
  ok := c11 && ok
  -- ---- CGB hardware ----
  -- synthetic CGB ROM: LD A,1 | LDH (KEY1),A | STOP | NOP | JR -2
  let blank := ByteArray.mk (Array.mk (List.replicate 0x8000 0))
  let poke (b : ByteArray) (base : Nat) (xs : List Nat) : ByteArray :=
    xs.foldl (fun (acc : ByteArray × Nat) v =>
      (bset acc.1 acc.2 (w8 v), acc.2 + 1)) (b, base) |>.1
  let cgbCode : List Nat :=
    [0x3E, 0x01,  -- LD A,0x01 (arm speed switch)
     0xE0, 0x4D,  -- LDH (0xFF4D),A
     0x10, 0x00,  -- STOP (switches speed, does not halt)
     0x00,        -- NOP
     0x18, 0xFE]  -- loop: JR -2
  let g0 := poke blank 0x0100 cgbCode
  let g1 := poke g0 0x0143 [0x80]  -- CGB-compatible flag
  let g2 := poke g1 0x0147 [0x00, 0x00, 0x00]
  let g := loadROM g2
  let c12 ← check "CGB cartridge detected" g.cgb
  ok := c12 && ok
  let c13 ← check "CGB boot A=0x11" (g.regs.a == 0x11)
  ok := c13 && ok
  -- WRAM banking: banks 2/3 isolated at 0xD000, bank 0 fixed
  let (w1, _) := busWrite g 0xFF70 0x02
  let (w2, _) := busWrite w1 0xD000 0xAA
  let (w3, _) := busWrite w2 0xFF70 0x03
  let (w4, _) := busWrite w3 0xD000 0xBB
  let (w5, _) := busWrite w4 0xC000 0xCC
  let (w6, _) := busWrite w5 0xFF70 0x02
  let c14 ← check "WRAM bank 2 isolated" (busRead w6 0xD000 == 0xAA)
  ok := c14 && ok
  let (w7, _) := busWrite w6 0xFF70 0x03
  let c15 ← check "WRAM bank 3 isolated" (busRead w7 0xD000 == 0xBB)
  ok := c15 && ok
  let c16 ← check "WRAM bank 0 fixed" (busRead w7 0xC000 == 0xCC)
  ok := c16 && ok
  -- VRAM banking
  let (v1, _) := busWrite g 0xFF4F 0x01
  let (v2, _) := busWrite v1 0x8000 0x12
  let (v3, _) := busWrite v2 0xFF4F 0x00
  let c17 ← check "VRAM bank 0 untouched" (busRead v3 0x8000 == 0x00)
  ok := c17 && ok
  let (v4, _) := busWrite v3 0xFF4F 0x01
  let c18 ← check "VRAM bank 1 isolated" (busRead v4 0x8000 == 0x12)
  ok := c18 && ok
  -- palette auto-increment write + readback
  let (p1, _) := busWrite g 0xFF68 0x80
  let (p2, _) := busWrite p1 0xFF69 0x1F
  let (p3, _) := busWrite p2 0xFF69 0x7C
  let c19 ← check "BGPI auto-incremented to 0x82" (p3.bgpi == 0x82)
  ok := c19 && ok
  let c20 ← check "BG pal0 == 0x7C1F" (p3.bgPal[0]! == 0x7C1F)
  ok := c20 && ok
  let (p4, _) := busWrite p3 0xFF68 0x00
  let c21 ← check "BGPD readback low byte" (busRead p4 0xFF69 == 0x1F)
  ok := c21 && ok
  -- KEY1 readback after arming
  let (k1, _) := busWrite g 0xFF4D 0x01
  let c22 ← check "KEY1 prep readable" (busRead k1 0xFF4D == 0x7F)
  ok := c22 && ok
  -- STOP performs the speed switch (3 instrs: LD A / LDH / STOP)
  let g3 := runInstrs g 3
  let c23 ← check "STOP switched to double speed" (g3.doubleSpeed && !g3.speedPrep)
  ok := c23 && ok
  let c24 ← check "STOP advanced past 2-byte opcode" (g3.regs.pc == 0x0106)
  ok := c24 && ok
  let c25 ← check "double-speed frame takes ~35k M-cycles"
    (let gf := runFrame g3; gf.cycles - g3.cycles > 30000)
  ok := c25 && ok
  -- GDMA: copy 16 bytes WRAM bank 1 → VRAM bank 0
  let (d0, _) := busWrite g 0xFF70 0x01
  let d1 := (List.range 16).foldl (fun st i =>
    (busWrite st (w16 (0xD000 + i)) (w8 (0x40 + i))).1) d0
  let (d2, _) := busWrite d1 0xFF51 0xD0
  let (d3, _) := busWrite d2 0xFF52 0x00
  let (d4, _) := busWrite d3 0xFF53 0x00
  let (d5, _) := busWrite d4 0xFF54 0x00
  let (d6, _) := busWrite d5 0xFF4F 0x00
  let (d7, cost) := busWrite d6 0xFF55 0x00
  let gdmaOk := (List.range 16).all fun i =>
    busRead d7 (w16 (0x8000 + i)) == w8 (0x40 + i)
  let c26 ← check "GDMA copied 16 bytes to VRAM" gdmaOk
  ok := c26 && ok
  let c27 ← check "GDMA cost 8 M-cycles + idle HDMA"
    (cost == 8 && d7.hdma.remaining == 0 && !d7.hdma.active)
  ok := c27 && ok
  -- HBlank DMA completes across a frame
  let (h0, _) := busWrite d7 0xFF55 0x80
  let h1 := runFrame h0
  let c28 ← check "HBlank DMA finished" (!h1.hdma.active && h1.hdma.remaining == 0)
  ok := c28 && ok
  -- CGB scanline renders white from fresh palettes/zero VRAM
  let c29 ← check "CGB framebuffer renders white"
    ((runFrame g).fb[0]! == 0xFFFFFFFF)
  ok := c29 && ok
  -- CGB sprite-vs-BG truth table (Pan Docs: BG wins iff opaque +
  -- master + EITHER prio bit). BG tile1 = solid idx1 (red pal0c1),
  -- sprite tile0 = solid idx3 (green obpal0c3) covering pixel (0,0).
  let mkVram (attrB : Nat) : ByteArray :=
    let z := ByteArray.mk (Array.mk (List.replicate 0x4000 0))
    let t0 := (List.range 16).foldl (fun b i => bset b i 0xFF) z
    let t1 := (List.range 8).foldl (fun b i =>
      bset (bset b (16 + i * 2) 0xFF) (16 + i * 2 + 1) 0x00) t0
    bset (bset t1 0x1800 0x01) (0x2000 + 0x1800) (w8 attrB)
  let mkOam (attrS : Nat) : ByteArray :=
    bset (bset (bset (bset
      (ByteArray.mk (Array.mk (List.replicate 160 0))) 0 16) 1 8) 2 0) 3 (w8 attrS)
  let bgP := palSet palFresh 1 0x001F
  let obP := palSet palFresh 3 0x03E0
  let ppu0 : PpuState := { ({} : PpuState) with lcdc := 0x93 }
  let px (sa ba : Nat) : UInt32 :=
    (PpuState.renderLineCgb ppu0 (mkVram ba) (mkOam sa) bgP obP)[0]!
  let red := cgbColor 0x001F
  let green := cgbColor 0x03E0
  let c30 ← check "CGB prio (S=1,B=0) → BG wins" (px 0x80 0x00 == red)
  ok := c30 && ok
  let c31 ← check "CGB prio (S=0,B=0) → sprite wins" (px 0x00 0x00 == green)
  ok := c31 && ok
  let c32 ← check "CGB prio (S=0,B=1) → BG wins" (px 0x00 0x80 == red)
  ok := c32 && ok
  let c33 ← check "CGB prio (S=1,B=1) → BG wins" (px 0x80 0x80 == red)
  ok := c33 && ok
  if ok then IO.println "[test] ALL PASS" else IO.Process.exit 1
