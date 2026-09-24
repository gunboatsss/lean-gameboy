/-
  agb-test — headless hello-world for the GBA core (synthetic Thumb ROM).

  Program (loaded at 0x08000000):
      MOVS r0,#0x45 | MOVS r1,#0x38 | ADDS r2,r0,r1   ; r2 = 0x7D
      LDR r3,[PC,#8]   ; r3 = 0x02000000 (literal at +0x10)
      STR r2,[r3,#0]   ; [EWRAM 0] = 0x7D
      loop: B loop
  Expected: EWRAM[0..3] = 7D 00 00 00, PC spins, one frame = 280896
  cycles with VBlank IRQ, timer0 overflow raises IF.3.
-/
import LeanAGB

open AGB
open AGB.Sdl

set_option maxHeartbeats 1000000

/-- Assemble the synthetic test ROM (literal pool at offset 0x10). -/
def testROM : ByteArray :=
  let code : List Nat :=
    [0x45, 0x20,   -- MOVS r0,#0x45
     0x38, 0x21,   -- MOVS r1,#0x38
     0x42, 0x18,   -- ADDS r2,r0,r1
     0x02, 0x4B,   -- LDR r3,[PC,#8]
     0x1A, 0x60,   -- STR r2,[r3,#0]
     0xFE, 0xE7,   -- loop: B -4
     0x00, 0x00,   -- padding (LSL r0,r0,#0)
     0x00, 0x00,   -- padding
     0x00, 0x00, 0x00, 0x02]  -- literal: 0x02000000 LE
  ByteArray.mk (Array.mk (code.map (fun n => w8 n)))

/-- Phase-B program: Thumb BX into ARM code (literal at 0x08,
    ARM entry at 0x0C, pass label at 0x24). -/
def testROM3 : ByteArray :=
  let code : List Nat :=
    [0x01, 0x48,   -- 0x00 LDR r0,[PC,#4]   ; → [0x08]
     0x00, 0x47,   -- 0x02 BX r0            ; → ARM @0x0C
     0xFE, 0xE7,   -- 0x04 trap
     0x00, 0x00,   -- 0x06 pad
     0x0C, 0x00, 0x00, 0x08,  -- 0x08 literal 0x0800000C
     0x45, 0x00, 0xA0, 0xE3,  -- 0x0C MOV r0,#0x45
     0x38, 0x10, 0x80, 0xE2,  -- 0x10 ADD r1,r0,#0x38
     0x7D, 0x00, 0x51, 0xE3,  -- 0x14 CMP r1,#0x7D
     0x00, 0x00, 0x00, 0x1A,  -- 0x18 BNE → 0x20 (not taken)
     0x00, 0x00, 0x00, 0x0A,  -- 0x1C BEQ → 0x24 (taken)
     0xFE, 0xFF, 0xFF, 0xEA,  -- 0x20 fail spin
     0x01, 0x20, 0xA0, 0xE1,  -- 0x24 MOV r2,r1
     0xFE, 0xFF, 0xFF, 0xEA]  -- 0x28 done spin
  ByteArray.mk (Array.mk (code.map (fun n => w8 n)))

def check (name : String) (cond : Bool) : IO Bool := do
  IO.println s!"[agb-test] {name}: {if cond then "PASS" else "FAIL"}"
  pure cond

/-- Blit byte list `bs` at `base` (test-data setup). -/
def blit : AGBState → Nat → List Nat → AGBState
  | s, _, [] => s
  | s, base, b :: bs => blit (memWrite8 s (w32 base) (w8 b)) (base + 1) bs

/-- Bits of a byte, MSB first. -/
def byteBits (b : Nat) : List Nat :=
  (List.range 8).map (fun i => (b >>> (7 - i)) &&& 1)

/-- Clock bit list into the EEPROM window (bit = D0 of each write). -/
def eew (s : AGBState) (bs : List Nat) : AGBState :=
  bs.foldl (fun s bit => memWrite8 s 0x0D000000 (w8 bit)) s

/-- Clock `n` bits out of the EEPROM window (D0 masked). -/
def eer : AGBState → Nat → AGBState × List Nat
  | s, 0 => (s, [])
  | s, k + 1 =>
    let (s, b) := memRead8E s 0x0D000000
    let (s, bs) := eer s k
    (s, (b.toNat &&& 1) :: bs)

/-- First byte (MSB-first bits) of a bit list. -/
def bitsByte (bs : List Nat) : Nat :=
  (List.range 8).foldl (fun acc i => acc * 2 + (bs.getD i 0)) 0

/-- Phase-A program: BEQ/MUL/LSR/SP/PUSH/POP/BL (offsets verified by
    `decode_*` proofs; literal pool at 0x20, subroutine at 0x24). -/
def testROM2 : ByteArray :=
  let code : List Nat :=
    [0x01, 0x20,   -- 0x00 MOVS r0,#1
     0x01, 0x28,   -- 0x02 CMP r0,#1        ; Z=1
     0x00, 0xD0,   -- 0x04 BEQ → 0x08       ; taken
     0xAA, 0x20,   -- 0x06 MOVS r0,#0xAA    ; skipped
     0x55, 0x21,   -- 0x08 MOVS r1,#0x55
     0x06, 0x22,   -- 0x0A MOVS r2,#6
     0x07, 0x23,   -- 0x0C MOVS r3,#7
     0x5A, 0x43,   -- 0x0E MUL r2,r3        ; r2 = 42
     0x80, 0x08,   -- 0x10 LSR r0,r0,#2     ; r0 = 0, C = 0
     0x03, 0x4C,   -- 0x12 LDR r4,[PC,#12]  ; → 0x20
     0xA5, 0x46,   -- 0x14 MOV SP,r4        ; SP = 0x02000010
     0x03, 0xB4,   -- 0x16 PUSH {r0,r1}
     0x60, 0xBC,   -- 0x18 POP {r5,r6}      ; r5 = 0, r6 = 0x55
     0x00, 0xF0,   -- 0x1A BL-pre (LR = 0x1E)
     0x03, 0xF8,   -- 0x1C BL-suf → 0x24    ; ret = 0x1F
     0xFE, 0xE7,   -- 0x1E spin
     0x10, 0x00, 0x00, 0x02,  -- 0x20 literal 0x02000010
     0x01, 0x27,   -- 0x24 MOVS r7,#1
     0x70, 0x47]   -- 0x26 BX LR → 0x1E
  ByteArray.mk (Array.mk (code.map (fun n => w8 n)))

set_option maxRecDepth 10000 in
def main : IO Unit := do
  let s0 := loadROM testROM
  let mut ok := true
  let c0 ← check "direct-boot PC=0x08000000 Thumb" (s0.regs.pc == 0x08000000 && cpsrT s0.regs.cpsr)
  ok := c0 && ok
  let s1 := runInstrs s0 5
  let c1 ← check "ADDS r2 == 0x7D" (s1.regs.get 2 == 0x7D)
  ok := c1 && ok
  let c2 ← check "EWRAM[0] == 0x7D" (memRead32 s1 0x02000000 == 0x7D)
  ok := c2 && ok
  let c3 ← check "Z flag clear (nonzero result)" (!cpsrZ s1.regs.cpsr)
  ok := c3 && ok
  let s2 := runInstrs s0 6
  let c4 ← check "PC spins in B loop" (s2.regs.pc == 0x0800000A)
  ok := c4 && ok
  -- one frame: exactly 280896 cycles, frame+1, VBlank IRQ latched
  let s3 := runFrame s2
  let c5 ← check "frame advanced" (s3.ppu.frame == s2.ppu.frame + 1)
  ok := c5 && ok
  let c6 ← check "frame cost 280896 cycles" (s3.cycles - s2.cycles == 280896)
  ok := c6 && ok
  let c7 ← check "VBlank IRQ (IF.0) fired" (((s3.irq.if_ >>> 0) &&& 1) != 0)
  ok := c7 && ok
  -- timer0: reload 0xFF00, enable, prescale /1 → 65536 ticks overflow.
  -- 30000 B-loop instrs ≈ 90000 cycles ≥ 65536, so IF.3 must latch.
  let t0 := memWrite16 (memWrite16 s0 0x04000100 0xFF00) 0x04000102 0x80
  let t1 := runInstrs t0 30000
  let c8 ← check "timer0 overflow → IF.3" ((((t1.irq.if_ >>> 3) &&& 1) : UInt16) != 0)
  ok := c8 && ok
  -- SWI Halt parks the CPU but cycles keep flowing
  let h0 := (hleSwi s0 SWI_HALT).1
  let h1 := runInstrs h0 10
  let c9 ← check "halted CPU advances 10 cycles, PC frozen"
    (h1.halted && h1.regs.pc == s0.regs.pc && h1.cycles == 10)
  ok := c9 && ok
  -- ---- Phase A: full-Thumb program ----
  -- BEQ taken, MUL, LSR#2, SP setup via literal+hiMOV, PUSH/POP round
  -- trip, BL subroutine call + BX return.
  let sA := loadROM testROM2
  let sB := runInstrs sA 16
  -- BEQ taken: after 3 instrs r0 is still 1 (0xAA skipped); the later
  -- LSR turns it to 0 (not-taken would give 0xAA >> 2 = 0x2A).
  let c10 ← check "BEQ taken (r0 == 1, skipped 0xAA)"
    ((runInstrs sA 3).regs.get 0 == 1 && sB.regs.get 0 == 0)
  ok := c10 && ok
  let c11 ← check "MUL r2 == 42" (sB.regs.get 2 == 42)
  ok := c11 && ok
  let c12 ← check "POP round trip r5 == 0, r6 == 0x55"
    (sB.regs.get 5 == 0 && sB.regs.get 6 == 0x55)
  ok := c12 && ok
  let c13 ← check "SP restored to 0x02000010" (sB.regs.get 13 == 0x02000010)
  ok := c13 && ok
  let c14 ← check "BL subroutine ran (r7 == 1, PC back at spin)"
    (sB.regs.get 7 == 1 && sB.regs.pc == 0x0800001E)
  ok := c14 && ok
  let c15 ← check "LSR carry cleared and preserved" (!cpsrC sB.regs.cpsr)
  ok := c15 && ok
  -- ---- Phase C: exception entry at runtime ----
  -- unknown SWI takes the real SVC vector (known ones still HLE above)
  let sU := loadROM (ByteArray.mk #[0xFF, 0xDF])
  let sV := runInstrs sU 1
  let c16 ← check "unknown SWI → SVC vector 0x08" (sV.regs.pc == 0x08)
  ok := c16 && ok
  let c17 ← check "SVC entry mode + LR"
    (cpsrMode sV.regs.cpsr == 0x13 && sV.regs.r14_svc == 0x08000004)
  ok := c17 && ok
  -- SVC round trip restores mode and resume address
  let sW := serviceSwi s0 0x08000000
  let sX := excReturn sW sW.regs.spsr_svc sW.regs.r14_svc
  let c18 ← check "SVC round trip restores SYS + PC"
    (sX.regs.cpsr == 0x3F && sX.regs.pc == 0x08000004)
  ok := c18 && ok
  -- ---- Phase B: ARM-mode program (BX in, DataProc + cond branches) ----
  let sY := loadROM testROM3
  let sZ := runInstrs sY 9
  let c19 ← check "ARM MOV/ADD r0/r1 == 0x45/0x7D"
    (sZ.regs.get 0 == 0x45 && sZ.regs.get 1 == 0x7D)
  ok := c19 && ok
  let c20 ← check "ARM branches (BNE skip, BEQ take) land at done"
    (sZ.regs.get 2 == 0x7D && sZ.regs.pc == 0x08000028)
  ok := c20 && ok
  let c21 ← check "ARM state kept, Z set by CMP"
    (!cpsrT sZ.regs.cpsr && cpsrZ sZ.regs.cpsr)
  ok := c21 && ok
  -- ---- Phase D: memory system ----
  -- unaligned loads rotate (b4 == b0 by construction)
  let sU := loadROM (ByteArray.mk #[0x11, 0x22, 0x33, 0x44, 0x11])
  let c22 ← check "unaligned LDR rotates"
    (memRead32 sU 0x08000001 == rotr32 (memRead32 sU 0x08000000) 8)
  ok := c22 && ok
  -- EWRAM mirror: write canonical, read mirror (full-size arrays)
  let sM := memWrite8 s0 0x02000000 0x42
  let c23 ← check "EWRAM mirror coherent" (memRead8 sM 0x02040000 == 0x42)
  ok := c23 && ok
  -- SRAM write/readback + .sav round trip (pure codec)
  let sS := memWrite8 s0 0x0E000123 0x42
  let c24 ← check "SRAM write/readback" (memRead8 sS 0x0E000123 == 0x42)
  ok := c24 && ok
  let sR := loadGame (loadROM testROM) (saveGame sS)
  let c25 ← check ".sav round trip preserves SRAM"
    (memRead8 sR 0x0E000123 == 0x42)
  ok := c25 && ok
  -- Flash byte program through the bus (AA/55/A0 + program)
  let sF := loadROM testROM
  let sF := { sF with save := SaveState.fresh .flash64 }
  let sF := memWrite8 sF 0x0E005555 0xAA
  let sF := memWrite8 sF 0x0E002AAA 0x55
  let sF := memWrite8 sF 0x0E005555 0xA0
  let sF := memWrite8 sF 0x0E000007 0x3C
  let c26 ← check "Flash program via command sequence"
    (memRead8 sF 0x0E000007 == 0x3C)
  ok := c26 && ok
  -- WAITCNT changes ROM timing (default N=4 → 5 cycles; N=2 → 3)
  let c27 ← check "default ROM16 cost 5" (memCost s0 0x08000000 16 == 5)
  ok := c27 && ok
  let sW := memWrite16 s0 0x04000204 0x0008
  let c28 ← check "WAITCNT WS0 N=2 → ROM16 cost 3"
    (memCost sW 0x08000000 16 == 3)
  ok := c28 && ok
  -- ---- Phase 0: IO sync (structs are source of truth) ----
  -- DISPCNT write lands in ppu + reads back live, Mode 3 renders
  let sD := memWrite16 s0 0x04000000 0x0403
  let c29 ← check "DISPCNT write syncs ppu" (sD.ppu.dispcnt == 0x0403)
  ok := c29 && ok
  let c30 ← check "DISPCNT live readback" (memRead16 sD 0x04000000 == 0x0403)
  ok := c30 && ok
  let sD2 := memWrite16 (memWrite16 sD 0x06000000 0x001F) 0x06000002 0x0000
  let fb := renderFrame sD2
  let c31 ← check "Mode3 renders when DISPCNT=3 (px0 red)"
    (fb.fb.getD 0 0 == 0xFFFF0000)
  ok := c31 && ok
  -- DISPSTAT: RW bits stick, RO flags preserved; VCOUNT live
  let sE := memWrite16 s0 0x04000004 0xFF38
  let c32 ← check "DISPSTAT RW bits (0xFF38)" (sE.ppu.dispstat == 0xFF38)
  ok := c32 && ok
  let c33 ← check "VCOUNT live read after frame"
    (memRead16 s3 0x04000006 == s3.ppu.vcount)
  ok := c33 && ok
  -- VBlank flag is live (set while vc in 160..227, clear after wrap)
  let rec toVBlank : AGBState → Nat → AGBState
    | st, 0 => st
    | st, k + 1 => if st.ppu.vcount.toNat == 160 then st else toVBlank (stepCPU st) k
  let sV := toVBlank s2 300000
  let c34 ← check "VBlank flag set in DISPSTAT during VBlank"
    (sV.ppu.vcount == 160 && ((sV.ppu.dispstat &&& 1) != 0))
  ok := c34 && ok
  -- Timer1 regs sync (reload + ctrl), cnt live-reads 0 at rest
  let sT := memWrite16 (memWrite16 s0 0x04000104 0x1234) 0x04000106 0x00C1
  let c35 ← check "TM1 reload/ctrl sync"
    ((sT.timers.ch.getD 1 {}).reload == 0x1234 && (sT.timers.ch.getD 1 {}).ctrl == 0x00C1)
  ok := c35 && ok
  let c36 ← check "TM1 cnt live reads reload after start edge"
    (memRead16 sT 0x04000104 == 0x1234
      && memRead16 s0 0x04000104 == 0)
  ok := c36 && ok
  -- DMA0 SAD/DAD/CNT lanes sync through 16-bit halves; immediate
  -- enable fires at once (enable auto-clears, SAD advanced past 1 unit)
  let sG := memWrite16 (memWrite16 (memWrite16 s0 0x040000B0 0x1111) 0x040000B2 0x0200) 0x040000B8 1
  let sG := memWrite16 sG 0x040000BA 0x8000
  let c37 ← check "DMA0 SAD32 sync + immediate fire clears enable"
    ((sG.dma.ch.getD 0 {}).sad == 0x02001113
      && (((sG.dma.ch.getD 0 {}).cnt_h >>> 15) &&& 1) == 0)
  ok := c37 && ok
  -- KEYCNT + IE/IF live readback
  let sK := memWrite16 s0 0x04000132 0x4000
  let c38 ← check "KEYCNT sync + live read"
    (sK.key.cnt == 0x4000 && memRead16 sK 0x04000132 == 0x4000)
  ok := c38 && ok
  -- ---- Phase 1: cascade timers, DMA, VCounter IRQ, masked wait ----
  -- TM0 overflow feeds TM1 count-up (reload + IF.3, TM1 cnt 1, no IF.4)
  let mkT0 := { (s0.timers.ch.getD 0 {}) with reload := 0, cnt := 0xFFFF, ctrl := 0x80, acc := 0 }
  let mkT1 := { (s0.timers.ch.getD 1 {}) with reload := 0xBEEF, cnt := 0, ctrl := 0x84, acc := 0 }
  let sT := { s0 with timers := { ch := (s0.timers.ch.set! 0 mkT0).set! 1 mkT1 } }
  let sT2 := stepTimers sT 1
  let c39 ← check "cascade: TM0 reloads, TM1 ticks, IF.3 only"
    ((sT2.timers.ch.getD 0 {}).cnt == 0 && (sT2.timers.ch.getD 1 {}).cnt == 1
      && sT2.irq.if_ == 0x08)
  ok := c39 && ok
  -- Immediate DMA0: 4 halfwords EWRAM→EWRAM, enable clears, no IRQ
  let sM0 := memWrite16 (memWrite16 s0 0x02000100 0x1111) 0x02000102 0x2222
  let sM0 := memWrite16 (memWrite16 sM0 0x02000104 0x3333) 0x02000106 0x4444
  let sM0 := memWrite16 (memWrite16 (memWrite16 sM0 0x040000B0 0x0100) 0x040000B2 0x0200) 0x040000B4 0x0200
  let sM0 := memWrite16 (memWrite16 sM0 0x040000B6 0x0200) 0x040000B8 4
  let sM0 := memWrite16 sM0 0x040000BA 0x8000
  let c40 ← check "DMA0 immediate copy + enable clear"
    (memRead16 sM0 0x02000200 == 0x1111 && memRead16 sM0 0x02000202 == 0x2222
      && memRead16 sM0 0x02000204 == 0x3333 && memRead16 sM0 0x02000206 == 0x4444
      && (((sM0.dma.ch.getD 0 {}).cnt_h >>> 15) &&& 1) == 0 && sM0.irq.if_ == 0)
  ok := c40 && ok
  -- CNT_H bus reads are live (post-fire enable reads clear, not shadow)
  let c40b ← check "DMA0 CNT_H live readback"
    (memRead16 sM0 0x040000BA == 0x0000)
  ok := c40b && ok
  -- DMA1 with IRQ bit: IF.9 latches on completion
  let sM1 := memWrite16 (memWrite16 sM0 0x040000BC 0x0100) 0x040000BE 0x0200
  let sM1 := memWrite16 (memWrite16 sM1 0x040000C0 0x0200) 0x040000C2 0x0200
  let sM1 := memWrite16 (memWrite16 sM1 0x040000C4 1) 0x040000C6 0xC000
  let c41 ← check "DMA1 IRQ completion IF.9"
    ((((sM1.irq.if_ >>> 9) &&& 1) : UInt16) != 0
      && memRead16 sM1 0x02000200 == 0x1111)
  ok := c41 && ok
  -- DMA2 fixed-src fill: 4× 0x00FF spread from one halfword
  let sM2 := memWrite16 s0 0x02000300 0x00FF
  let sM2 := memWrite16 (memWrite16 sM2 0x040000C8 0x0300) 0x040000CA 0x0200
  let sM2 := memWrite16 (memWrite16 sM2 0x040000CC 0x0400) 0x040000CE 0x0200
  let sM2 := memWrite16 (memWrite16 sM2 0x040000D0 4) 0x040000D2 0x8100
  let c42 ← check "DMA2 fixed-src fill"
    (memRead16 sM2 0x02000400 == 0x00FF && memRead16 sM2 0x02000406 == 0x00FF
      && memRead32 sM2 0x02000400 == memRead32 sM2 0x02000404)
  ok := c42 && ok
  -- DMA3 VBlank-timed: no copy until line 160, then fires once
  let sV0 := memWrite16 s0 0x02000500 0xABCD
  let sV0 := memWrite16 (memWrite16 sV0 0x040000D4 0x0500) 0x040000D6 0x0200
  let sV0 := memWrite16 (memWrite16 sV0 0x040000D8 0x0600) 0x040000DA 0x0200
  let sV0 := memWrite16 (memWrite16 sV0 0x040000DC 1) 0x040000DE 0x9000
  let c43 ← check "VBlank DMA pending (no early copy)"
    (memRead16 sV0 0x02000500 == 0xABCD && memRead16 sV0 0x02000600 == 0
      && (((sV0.dma.ch.getD 3 {}).cnt_h >>> 15) &&& 1) == 1)
  ok := c43 && ok
  let sV1 := runFrame sV0
  let c44 ← check "VBlank DMA fired during frame"
    (memRead16 sV1 0x02000600 == 0xABCD
      && (((sV1.dma.ch.getD 3 {}).cnt_h >>> 15) &&& 1) == 0)
  ok := c44 && ok
  -- DMA bulk fast path: fires on linear increment windows, declines IO
  let c44b ← check "DMA bulk fires (EWRAM→EWRAM)"
    ((dmaBulk s0 0x02000100 0x02000200 8).isSome)
  ok := c44b && ok
  let c44c ← check "DMA bulk fires (ROM→VRAM)"
    ((dmaBulk s0 0x08000000 0x06000000 8).isSome)
  ok := c44c && ok
  let c44d ← check "DMA bulk declines (RAM→FIFO)"
    ((dmaBulk s0 0x02000100 0x040000A0 8).isNone)
  ok := c44d && ok
  -- DMA0 immediate ROM→VRAM bulk: exact bytes (testROM LE halfwords)
  let sR := memWrite16 (memWrite16 s0 0x040000B0 0x0000) 0x040000B2 0x0800
  let sR := memWrite16 (memWrite16 sR 0x040000B4 0x0000) 0x040000B6 0x0600
  let sR := memWrite16 sR 0x040000B8 4
  let sR := memWrite16 sR 0x040000BA 0x8000
  let c44e ← check "DMA ROM→VRAM bulk exact bytes"
    (memRead16 sR 0x06000000 == 0x2045 && memRead16 sR 0x06000002 == 0x2138
      && memRead16 sR 0x06000004 == 0x1842 && memRead16 sR 0x06000006 == 0x4B02
      && (((sR.dma.ch.getD 0 {}).cnt_h >>> 15) &&& 1) == 0)
  ok := c44e && ok
  -- VCounter IRQ: DISPSTAT setting 10 + enable → IF.2 at vc == 10
  let sC := memWrite16 s0 0x04000004 0x0A20
  let rec toVCount : AGBState → Nat → AGBState
    | st, 0 => st
    | st, k + 1 => if st.ppu.vcount.toNat == 10 then st else toVCount (stepCPU st) k
  let sC2 := toVCount sC 30000
  let c45 ← check "VCounter match sets IF.2"
    (sC2.ppu.vcount == 10 && (((sC2.irq.if_ >>> 2) &&& 1) : UInt16) != 0)
  ok := c45 && ok
  -- VBlankWait parks and wakes on the next VBlank (needs IE.0, like HW)
  let sH0 := memWrite16 s0 0x04000200 0x0001
  let sH := (hleSwi sH0 SWI_VBLANKWAIT).1
  let c46 ← check "VBlankWait parks CPU" (sH.halted && sH.waitMask == 1)
  ok := c46 && ok
  let sH2 := runFrame sH
  let c47 ← check "VBlankWait wakes after frame" (!sH2.halted)
  ok := c47 && ok
  -- IntrWait with TM0-only mask stays parked (TM0 disabled, VBlank masked out)
  let sI0 := memWrite16 s0 0x04000200 0x00FF
  let sI0 := { sI0 with regs := sI0.regs.set 1 0x08 }
  let sI := (hleSwi sI0 SWI_INTRWAIT).1
  let sI2 := runFrame sI
  let c48 ← check "IntrWait mask excludes VBlank (still parked)"
    (sI2.halted && sI2.irq.if_ != 0)
  ok := c48 && ok
  -- ---- Phase 2: BIOS HLE (GBATEK-verified semantics) ----
  -- CpuSet 16-bit copy: r0=src r1=dst r2=count
  let sP0 := memWrite16 (memWrite16 s0 0x02001000 0xAAAA) 0x02001002 0x5555
  let sP0 := { sP0 with regs := ((sP0.regs.set 0 0x02001000).set 1 0x02001100).set 2 2 }
  let sP1 := (hleSwi sP0 SWI_CPUSET).1
  let c49 ← check "CpuSet16 copy"
    (memRead16 sP1 0x02001100 == 0xAAAA && memRead16 sP1 0x02001102 == 0x5555)
  ok := c49 && ok
  -- CpuSet 32-bit (bit26) + fill (bit24): one word spread 3×
  let sP2 := memWrite32 s0 0x02001200 0xDEADBEEF
  let sP2 := { sP2 with regs := ((sP2.regs.set 0 0x02001200).set 1 0x02001300).set 2 0x5000003 }
  let sP3 := (hleSwi sP2 SWI_CPUSET).1
  let c50 ← check "CpuSet32 fill ×3"
    (memRead32 sP3 0x02001300 == 0xDEADBEEF && memRead32 sP3 0x02001308 == 0xDEADBEEF)
  ok := c50 && ok
  -- CpuSet refuses BIOS-area sources silently
  let sP4 := { s0 with regs := ((s0.regs.set 0 0x00000100).set 1 0x02001400).set 2 4 }
  let sP5 := (hleSwi sP4 SWI_CPUSET).1
  let c51 ← check "CpuSet BIOS-src refuse (no write)"
    (memRead32 sP5 0x02001400 == 0)
  ok := c51 && ok
  -- CpuFastSet fill: count 1 rounds up to 8 words, all filled
  let sP6 := memWrite32 s0 0x02001500 0x12345678
  let sP6 := { sP6 with regs := ((sP6.regs.set 0 0x02001500).set 1 0x02001600).set 2 0x1000001 }
  let sP7 := (hleSwi sP6 SWI_CPUFASTSET).1
  let c52 ← check "CpuFastSet fill round-up ×8"
    (memRead32 sP7 0x02001600 == 0x12345678 && memRead32 sP7 0x0200161C == 0x12345678)
  ok := c52 && ok
  -- Div: -1234 / 10 = (-123, -4, 123); by zero → zeros
  let sDv := { s0 with regs := (s0.regs.set 0 0xFFFFFB2E).set 1 10 }
  let sDv2 := (hleSwi sDv SWI_DIV).1
  let c53 ← check "Div -1234/10"
    (sDv2.regs.get 0 == 0xFFFFFF85 && sDv2.regs.get 1 == 0xFFFFFFFC && sDv2.regs.get 3 == 123)
  ok := c53 && ok
  let sDz := { s0 with regs := (s0.regs.set 0 100).set 1 0 }
  let sDz2 := (hleSwi sDz SWI_DIV).1
  let c54 ← check "Div by zero → zeros (no hang)"
    (sDz2.regs.get 0 == 0 && sDz2.regs.get 1 == 0 && sDz2.regs.get 3 == 0)
  ok := c54 && ok
  -- DivArm swaps operands: r0=den 10, r1=num -1234
  let sDa := { s0 with regs := (s0.regs.set 0 10).set 1 0xFFFFFB2E }
  let sDa2 := (hleSwi sDa SWI_DIVARM).1
  let c55 ← check "DivArm swapped"
    (sDa2.regs.get 0 == 0xFFFFFF85 && sDa2.regs.get 3 == 123)
  ok := c55 && ok
  -- Sqrt: 2^24 → 4096, 2 → 1
  let sSq := { s0 with regs := s0.regs.set 0 0x01000000 }
  let sSq2 := (hleSwi sSq SWI_SQRT).1
  let c56 ← check "Sqrt(2^24) = 4096" (sSq2.regs.get 0 == 4096)
  ok := c56 && ok
  -- RegisterRamReset bit2 clears palette + forces DISPCNT 0x80
  let sR0 := memWrite8 s0 0x05000000 0xFF
  let sR0 := { sR0 with regs := sR0.regs.set 0 0x04 }
  let sR1 := (hleSwi sR0 SWI_REGRAMRESET).1
  let c57 ← check "RegReset palette clear + forced blank"
    (memRead8 sR1 0x05000000 == 0 && sR1.ppu.dispcnt == 0x0080
      && memRead16 sR1 0x04000000 == 0x0080)
  ok := c57 && ok
  -- RegisterRamReset bit1 clears IWRAM but preserves top 0x200
  let sR2 := memWrite8 (memWrite8 s0 0x03000000 0x42) 0x03007F00 0x77
  let sR2 := { sR2 with regs := sR2.regs.set 0 0x02 }
  let sR3 := (hleSwi sR2 SWI_REGRAMRESET).1
  let c58 ← check "RegReset IWRAM keeps top 512B"
    (memRead8 sR3 0x03000000 == 0 && memRead8 sR3 0x03007F00 == 0x77)
  ok := c58 && ok
  -- SoftReset flag 0 → ROM/ARM, stacks installed, top cleared
  let sS0 := memWrite8 (memWrite8 s0 0x03007FFA 0) 0x03007E00 0x42
  let sS0 := { sS0 with regs := (sS0.regs.set 0 0xDEAD).set 15 0x08000100 }
  let sS1 := (hleSwi sS0 SWI_SOFTRESET).1
  let c59 ← check "SoftReset → ROM ARM, regs zero, SPs set"
    (sS1.regs.pc == 0x08000000 && !cpsrT sS1.regs.cpsr
      && sS1.regs.get 0 == 0 && sS1.regs.get 14 == 0x08000000
      && sS1.regs.r13_svc == 0x03007FE0 && sS1.regs.r13_irq == 0x03007FA0
      && sS1.regs.get 13 == 0x03007F00 && memRead8 sS1 0x03007E00 == 0)
  ok := c59 && ok
  -- Stop parks like Halt
  let sSt := (hleSwi s0 SWI_STOP).1
  let c60 ← check "Stop parks CPU" (sSt.halted && sSt.waitMask == 0)
  ok := c60 && ok
  -- IntrWait r0=0 returns immediately when a masked flag is already set
  let sW0 := memWrite16 s0 0x04000200 0x00FF
  let sW0 := { sW0 with irq := { sW0.irq with if_ := 0x0008 } }
  let sW0 := { sW0 with regs := (sW0.regs.set 0 0).set 1 0x08 }
  let sW1 := (hleSwi sW0 SWI_INTRWAIT).1
  let c61 ← check "IntrWait r0=0 old flag → no park" (!sW1.halted)
  ok := c61 && ok
  -- ---- Phase 3: decompression + affine + arctan ----
  -- LZ77 literals: "ABCABCABC" (8 + 1 across two flag groups)
  let sL0 := blit s0 0x02002000
    [0x10, 0x09, 0, 0, 0x00, 0x41, 0x42, 0x43, 0x41, 0x42, 0x43, 0x41, 0x42, 0x00, 0x43]
  let sL0 := { sL0 with regs := (sL0.regs.set 0 0x02002000).set 1 0x02002100 }
  let sL1 := (hleSwi sL0 SWI_LZ77WRAM).1
  let c62 ← check "LZ77 literals ABCABCABC"
    (memRead32 sL1 0x02002100 == 0x41434241 && memRead32 sL1 0x02002104 == 0x42414342
      && memRead8 sL1 0x02002108 == 0x43)
  ok := c62 && ok
  -- LZ77 backref: flags 0x40 = literal then match(disp 1, len 3) = "AAAA"
  let sL2 := blit s0 0x02002200 [0x10, 0x04, 0, 0, 0x40, 0x41, 0x00, 0x00]
  let sL2 := { sL2 with regs := (sL2.regs.set 0 0x02002200).set 1 0x02002300 }
  let sL3 := (hleSwi sL2 SWI_LZ77WRAM).1
  let c63 ← check "LZ77 backref AAAA" (memRead32 sL3 0x02002300 == 0x41414141)
  ok := c63 && ok
  -- LZ77 Vram variant agrees on valid input
  let sL4 := (hleSwi sL2 SWI_LZ77VRAM).1
  let c64 ← check "LZ77 Vram same output" (memRead32 sL4 0x02002300 == 0x41414141)
  ok := c64 && ok
  -- Huff: root→{A,B} directly, stream 0,1 → "AB"
  let sH0 := blit s0 0x02003000
    [0x28, 0x02, 0, 0, 0x01, 0xC0, 0x41, 0x42, 0x00, 0x00, 0x00, 0x40]
  let sH0 := { sH0 with regs := (sH0.regs.set 0 0x02003000).set 1 0x02003100 }
  let sH1 := (hleSwi sH0 SWI_HUFF).1
  let c65 ← check "Huff AB"
    (memRead8 sH1 0x02003100 == 0x41 && memRead8 sH1 0x02003101 == 0x42)
  ok := c65 && ok
  -- RL: "ABC" + "DDDD" + 1 pad byte
  let sRl0 := blit s0 0x02003200
    [0x30, 0x07, 0, 0, 0x02, 0x41, 0x42, 0x43, 0x81, 0x44]
  let sRl0 := { sRl0 with regs := (sRl0.regs.set 0 0x02003200).set 1 0x02003300 }
  let sRl1 := (hleSwi sRl0 SWI_RLWRAM).1
  let c66 ← check "RL AB CDDDD + pad"
    (memRead32 sRl1 0x02003300 == 0x44434241 && memRead32 sRl1 0x02003304 == 0x00444444
      && memRead8 sRl1 0x02003307 == 0)
  ok := c66 && ok
  -- BitUnPack 1→8: 0xA5 = 10100101b, LSB-first units
  let sB0 := blit s0 0x02004000 [0xA5]
  let sB0 := blit sB0 0x02004100 [0x01, 0x00, 0x01, 0x08, 0, 0, 0, 0]
  let sB0 := { sB0 with regs := ((sB0.regs.set 0 0x02004000).set 1 0x02004200).set 2 0x02004100 }
  let sB1 := (hleSwi sB0 SWI_BITUNPACK).1
  let c67 ← check "BitUnPack 1→8"
    (memRead32 sB1 0x02004200 == 0x00010001 && memRead32 sB1 0x02004204 == 0x01000100)
  ok := c67 && ok
  -- BitUnPack with offset 5 (zero flag clear): nonzero units +5
  let sB2 := blit s0 0x02004000 [0xA5]
  let sB2 := blit sB2 0x02004100 [0x01, 0x00, 0x01, 0x08, 0x05, 0, 0, 0]
  let sB2 := { sB2 with regs := ((sB2.regs.set 0 0x02004000).set 1 0x02004300).set 2 0x02004100 }
  let sB3 := (hleSwi sB2 SWI_BITUNPACK).1
  let c68 ← check "BitUnPack offset (skip zero)"
    (memRead8 sB3 0x02004300 == 6 && memRead8 sB3 0x02004301 == 0
      && memRead8 sB3 0x02004305 == 6)
  ok := c68 && ok
  -- BitUnPack with zero flag: zero units +5 too
  let sB4 := blit s0 0x02004000 [0xA5]
  let sB4 := blit sB4 0x02004100 [0x01, 0x00, 0x01, 0x08, 0x05, 0, 0, 0x80]
  let sB4 := { sB4 with regs := ((sB4.regs.set 0 0x02004000).set 1 0x02004400).set 2 0x02004100 }
  let sB5 := (hleSwi sB4 SWI_BITUNPACK).1
  let c69 ← check "BitUnPack offset (with zero)"
    (memRead8 sB5 0x02004400 == 6 && memRead8 sB5 0x02004401 == 5)
  ok := c69 && ok
  -- Diff8: GBATEK example 10,11,12,13 from 10,+1,+1,+1
  let sF0 := blit s0 0x02004500 [0x81, 0x04, 0, 0, 10, 1, 1, 1]
  let sF0 := { sF0 with regs := (sF0.regs.set 0 0x02004500).set 1 0x02004600 }
  let sF1 := (hleSwi sF0 SWI_DIFF8W).1
  let c70 ← check "Diff8 10..13"
    (memRead32 sF1 0x02004600 == 0x0D0C0B0A)
  ok := c70 && ok
  -- Diff16: [0x1000, +2] → [0x1000, 0x1002]
  let sF2 := blit s0 0x02004700 [0x82, 0x04, 0, 0, 0x00, 0x10, 0x02, 0x00]
  let sF2 := { sF2 with regs := (sF2.regs.set 0 0x02004700).set 1 0x02004800 }
  let sF3 := (hleSwi sF2 SWI_DIFF16).1
  let c71 ← check "Diff16 accumulate"
    (memRead16 sF3 0x02004800 == 0x1000 && memRead16 sF3 0x02004802 == 0x1002)
  ok := c71 && ok
  -- BgAffine identity: PA=PD=0x100, rest 0
  let sA0 := blit s0 0x02005000
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x01, 0, 0x01, 0, 0, 0, 0]
  let sA0 := { sA0 with regs := ((sA0.regs.set 0 0x02005000).set 1 0x02005100).set 2 1 }
  let sA1 := (hleSwi sA0 SWI_BGAFFINE).1
  let c72 ← check "BgAffine identity"
    (memRead16 sA1 0x02005100 == 0x0100 && memRead16 sA1 0x02005102 == 0
      && memRead16 sA1 0x02005104 == 0 && memRead16 sA1 0x02005106 == 0x0100
      && memRead32 sA1 0x02005108 == 0 && memRead32 sA1 0x0200510C == 0)
  ok := c72 && ok
  -- BgAffine 90° (theta idx 64): PA=0 PB=-256 PC=256 PD=0
  let sA2 := blit s0 0x02005000
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x01, 0, 0x01, 0, 0x40, 0, 0]
  let sA2 := { sA2 with regs := ((sA2.regs.set 0 0x02005000).set 1 0x02005200).set 2 1 }
  let sA3 := (hleSwi sA2 SWI_BGAFFINE).1
  let c73 ← check "BgAffine 90°"
    (memRead16 sA3 0x02005200 == 0 && memRead16 sA3 0x02005202 == 0xFF00
      && memRead16 sA3 0x02005204 == 0x0100 && memRead16 sA3 0x02005206 == 0)
  ok := c73 && ok
  -- ObjAffine contiguous (offset 2) identity
  let sO0 := blit s0 0x02005300 [0, 0x01, 0, 0x01, 0, 0, 0, 0]
  let sO0 := { sO0 with regs := (((sO0.regs.set 0 0x02005300).set 1 0x02005400).set 2 1).set 3 2 }
  let sO1 := (hleSwi sO0 SWI_OBJAFFINE).1
  let c74 ← check "ObjAffine contiguous"
    (memRead32 sO1 0x02005400 == 0x00000100 && memRead32 sO1 0x02005404 == 0x01000000)
  ok := c74 && ok
  -- ObjAffine OAM stride (offset 8): A@0 B@8 C@16 D@24
  let sO2 := { sO0 with regs := (((sO0.regs.set 0 0x02005300).set 1 0x02005500).set 2 1).set 3 8 }
  let sO3 := (hleSwi sO2 SWI_OBJAFFINE).1
  let c75 ← check "ObjAffine OAM stride"
    (memRead16 sO3 0x02005500 == 0x0100 && memRead16 sO3 0x02005508 == 0
      && memRead16 sO3 0x02005510 == 0 && memRead16 sO3 0x02005518 == 0x0100)
  ok := c75 && ok
  -- ArcTan exact points: 0 → 0; fast paths preserved
  let sT0 := { s0 with regs := s0.regs.set 0 0 }
  let sT1 := (hleSwi sT0 SWI_ARCTAN).1
  let c76 ← check "ArcTan(0) = 0" (sT1.regs.get 0 == 0)
  ok := c76 && ok
  let sT2 := { s0 with regs := s0.regs.set 0 0x4000 }
  let sT3 := (hleSwi sT2 SWI_ARCTAN).1
  let c77 ← check "ArcTan(1.0) = 0x2000" (sT3.regs.get 0 == 0x2000)
  ok := c77 && ok
  let sT4 := { s0 with regs := (s0.regs.set 0 0x4000).set 1 0 }
  let sT5 := (hleSwi sT4 SWI_ARCTAN2).1
  let c78 ← check "ArcTan2(x>0,0) = 0, r3 = 0x170"
    (sT5.regs.get 0 == 0 && sT5.regs.get 3 == 0x170)
  ok := c78 && ok
  let sT6 := { s0 with regs := (s0.regs.set 0 0).set 1 0x4000 }
  let sT7 := (hleSwi sT6 SWI_ARCTAN2).1
  let c79 ← check "ArcTan2(0,y>0) = 0x4000" (sT7.regs.get 0 == 0x4000)
  ok := c79 && ok
  -- ---- Phase 4: Mode 0 backgrounds ----
  -- scene: pal{black,red,white}, tile0 red, tile2 white, maps at blk1/2
  let sP := blit s0 0x05000000 [0, 0, 0x1F, 0, 0xFF, 0x7F]
  let sP := blit sP 0x06000000 (List.replicate 32 0x11)
  let sP := blit sP 0x06000040 (List.replicate 32 0x22)
  let sP := blit sP 0x06000800 [0, 0, 1, 0]
  let sP := blit sP 0x06001000 [2, 0]
  let sP := memWrite16 (memWrite16 sP 0x04000000 0x0100) 0x04000008 0x0100
  let fB := (renderFrame sP).fb
  let c80 ← check "Mode0 BG0 red tile + backdrop"
    (fB.getD 0 0 == 0xFFFF0000 && fB.getD 8 0 == 0xFF000000)
  ok := c80 && ok
  -- scroll: HOFS 8 shifts tile1 (transparent) under x=0
  let sS := memWrite16 sP 0x04000010 8
  let c81 ← check "Mode0 HOFS scroll" ((renderFrame sS).fb.getD 0 0 == 0xFF000000)
  ok := c81 && ok
  -- priority: BG1 prio0 white beats BG0 prio1 red at x=0
  let sR := memWrite16 (memWrite16 sP 0x04000008 0x0101) 0x0400000A 0x0200
  let sR := memWrite16 sR 0x04000000 0x0300
  let c82 ← check "Mode0 priority BG1 wins" ((renderFrame sR).fb.getD 0 0 == 0xFFFFFFFF)
  ok := c82 && ok
  -- all layers off → backdrop everywhere
  let sN := memWrite16 sP 0x04000000 0x0000
  let c83 ← check "Mode0 backdrop" ((renderFrame sN).fb.getD 0 0 == 0xFF000000)
  ok := c83 && ok
  -- ---- Phase 5: OBJs (native pixel checks; kernel pins parse) ----
  -- scene: BG0 red tile, OBJ tile0 white + tile1 red/white halves
  let sO := blit s0 0x05000000 [0, 0, 0x1F, 0, 0xFF, 0x7F]
  let sO := blit sO 0x05000200 [0, 0, 0x1F, 0, 0xFF, 0x7F]
  let sO := blit sO 0x06000000 (List.replicate 32 0x11)
  let sO := blit sO 0x06000800 [0, 0, 1, 0]
  let sO := blit sO 0x06010000 (List.replicate 32 0x22)
  let sO := blit sO 0x06010020 (List.replicate 32 0x21)
  let sO := memWrite16 (memWrite16 sO 0x04000000 0x1100) 0x04000008 0x0100
  -- park entries 1-127 at Y=160 so entry0 tests are isolated
  let sO := (List.range 127).foldl
    (fun s i => memWrite8 s (w32 (0x07000008 + 8 * i)) 160) sO
  -- entry0 (fresh zeros) = 8x8 white tile0 at (0,0), wins tie at (4,4)
  let fO := (renderFrame sO).fb
  let c84 ← check "OBJ white over BG red"
    (fO.getD (4 * 240 + 4) 0 == 0xFFFFFFFF)
  ok := c84 && ok
  let c85 ← check "BG red beyond sprites"
    (fO.getD (100 * 240 + 100) 0 == 0xFFFF0000)
  ok := c85 && ok
  -- sprite prio 1 loses to BG prio 0
  let sO1 := memWrite16 sO 0x07000004 0x0400
  let c86 ← check "OBJ prio1 hidden by BG"
    ((renderFrame sO1).fb.getD (4 * 240 + 4) 0 == 0xFFFF0000)
  ok := c86 && ok
  -- disabled sprite stays hidden
  let sO2 := memWrite16 (memWrite16 sO1 0x07000004 0x0000) 0x07000000 0x0200
  let c87 ← check "OBJ disabled hidden"
    ((renderFrame sO2).fb.getD (4 * 240 + 4) 0 == 0xFFFF0000)
  ok := c87 && ok
  -- asymmetric tile1 at (20,20): left red, right white; then hflip
  let sO3 := blit sO2 0x07000008 [20, 0, 20, 0, 1, 0, 0, 0]
  let fO3 := (renderFrame sO3).fb
  let c88 ← check "OBJ asymmetric noflip"
    (fO3.getD (20 * 240 + 20) 0 == 0xFFFF0000
      && fO3.getD (20 * 240 + 27) 0 == 0xFFFFFFFF)
  ok := c88 && ok
  let sO4 := memWrite16 sO3 0x0700000A 0x1014
  let fO4 := (renderFrame sO4).fb
  let c89 ← check "OBJ hflip mirrors"
    (fO4.getD (20 * 240 + 20) 0 == 0xFFFFFFFF
      && fO4.getD (20 * 240 + 27) 0 == 0xFFFF0000)
  ok := c89 && ok
  -- ---- Phase 6: EEPROM serial backup (end-to-end bit protocol) ----
  -- write block 5 (addr 000101) with [A5,5A,0..0] through the bus
  let sE0 : AGBState := { loadROM testROM with save := SaveState.fresh .eeprom4k }
  let wdata : List Nat := [0xA5, 0x5A, 0, 0, 0, 0, 0, 0]
  let wbits := [1, 0] ++ [0, 0, 0, 1, 0, 1]
    ++ wdata.flatMap byteBits ++ [0]
  let sE1 := eew sE0 wbits
  -- read it back: header + trailing, then 4 lead zeros + 64 data bits
  let sE2 := eew sE1 ([1, 1] ++ [0, 0, 0, 1, 0, 1] ++ [0])
  let (sE3, lead) := eer sE2 4
  let (sE4, dat) := eer sE3 64
  let c90 ← check "EEPROM write→read round trip"
    (lead == [0, 0, 0, 0] && bitsByte dat == 0xA5
      && bitsByte (dat.drop 8) == 0x5A && bitsByte (dat.drop 16) == 0)
  ok := c90 && ok
  -- .sav codec preserves the programmed block
  let c91 ← check "EEPROM .sav round trip"
    (bget (saveDecode (saveGame sE4)).eeprom.data (5 * 8) == 0xA5
      && bget (saveDecode (saveGame sE4)).eeprom.data (5 * 8 + 1) == 0x5A)
  ok := c91 && ok
  -- executed LDRB clocks the stream: prime, bus-skip leads, exec, bus
  let sX0 : AGBState := { loadROM (ByteArray.mk #[0x20, 0x78, 0xFE, 0xE7])
    with save := SaveState.fresh .eeprom4k }
  let sX0 := eew sX0 wbits
  let sX0 := eew sX0 ([1, 1] ++ [0, 0, 0, 1, 0, 1] ++ [0])
  let (sX1, lead2) := eer sX0 4
  let okLead ← check "EEPROM lead zeros" (lead2 == [0, 0, 0, 0])
  ok := okLead && ok
  let sX2 := { sX1 with regs := sX1.regs.set 4 0x0D000000 }
  let sX3 := runInstrs sX2 1
  let c92 ← check "exec LDRB reads data bit 0"
    ((sX3.regs.get 0).toNat &&& 1 == 1)
  ok := c92 && ok
  let (_, nxt) := eer sX3 1
  let c93 ← check "exec advanced stream (next bit 0)"
    (nxt == [0])
  ok := c93 && ok
  -- ---- Phase 7: bitmap modes 4/5 + save autodetect ----
  -- mode 4: pal idx5 green; page 0 holds 5, page 1 holds 2 (blue)
  let sM4 := blit s0 0x05000000 [0, 0, 0, 0, 0, 0x7C, 0, 0, 0, 0, 0xE0, 0x03]
  let sM4 := memWrite8 (memWrite8 sM4 0x06000000 5) 0x0600A000 2
  let sM4 := memWrite16 sM4 0x04000000 0x0004
  let fM4 := (renderFrame sM4).fb
  let c94 ← check "Mode4 page0 green"
    (fM4.getD 0 0 == 0xFF00FF00 && fM4.getD 1 0 == 0xFF000000)
  ok := c94 && ok
  let sM4b := memWrite16 sM4 0x04000000 0x0014
  let c95 ← check "Mode4 page1 blue"
    ((renderFrame sM4b).fb.getD 0 0 == 0xFF0000FF)
  ok := c95 && ok
  -- mode 5: red at page-0 origin, white page-1 origin, backdrop past x=159
  let sM5 := blit s0 0x06000000 [0x1F, 0]
  let sM5 := blit sM5 0x0600A000 [0xFF, 0x7F]
  let sM5 := memWrite16 sM5 0x04000000 0x0005
  let fM5 := (renderFrame sM5).fb
  let c96 ← check "Mode5 page0 red + backdrop"
    (fM5.getD 0 0 == 0xFFFF0000 && fM5.getD 160 0 == 0xFF000000)
  ok := c96 && ok
  let sM5b := memWrite16 sM5 0x04000000 0x0015
  let c97 ← check "Mode5 page1 white"
    ((renderFrame sM5b).fb.getD 0 0 == 0xFFFFFFFF)
  ok := c97 && ok
  -- ---- Phase 8: IRQ dispatch through the embedded BIOS stub ----
  -- ARM handler at 0x08000100: STR r4,[r1] + BX lr; vector installed.
  -- (r0 is scratch: the stub legitimately clobbers/restores it.)
  let hrom := bset32LE (bset32LE
    (ByteArray.mk (Array.replicate 0x108 (0 : UInt8))) 0x100 0xE5814000) 0x104 0xE12FFF1E
  let sQ0 := loadROM hrom
  let sQ0 := { sQ0 with regs := ((sQ0.regs.set 0 0xDEAD).set 4 0x42).set 1 0x02000000 }
  let sQ0 := memWrite32 sQ0 0x03007FFC 0x08000100
  let sQ0 := memWrite16 sQ0 0x04000200 0x0001
  let sQ0 := { sQ0 with irq := { sQ0.irq with if_ := 1, ime := true } }
  let sQ1 := stepCPU sQ0
  let c99 ← check "IRQ entry via stub vector"
    (sQ1.regs.pc == 0x18 && cpsrMode sQ1.regs.cpsr == 0x12)
  ok := c99 && ok
  let sQ2 := runInstrs sQ1 9
  let c100 ← check "handler STR ran + exact resume"
    (memRead32 sQ2 0x02000000 == 0x42 && sQ2.regs.pc == 0x08000000
      && cpsrMode sQ2.regs.cpsr == 0x1F && cpsrT sQ2.regs.cpsr)
  ok := c100 && ok
  let c101 ← check "stub push/pop preserved regs"
    (sQ2.regs.get 0 == 0xDEAD && sQ2.regs.get 1 == 0x02000000
      && memRead32 sQ2 0x03007F88 == 0xDEAD)
  ok := c101 && ok
  -- ---- Phase 9: keypad input + KEYCNT IRQ ----
  let sK0 := loadROM testROM
  let sK1 := setButtons sK0 0x10
  let c99a ← check "A pressed in KEYINPUT"
    (sK1.key.input == 0x3FE && memRead16 sK1 0x04000130 == 0x03FE)
  ok := c99a && ok
  -- KEYCNT: enable + select A, press A → IF.12
  let sK2 := memWrite16 sK1 0x04000132 0x4001
  let sK3 := setButtons sK2 0x10
  let c99b ← check "KEYCNT OR fires IF.12"
    ((((sK3.irq.if_ >>> 12) &&& 1) : UInt16) != 0)
  ok := c99b && ok
  -- shoulder buttons: Q = L (bit 9), W = R (bit 8)
  let c99d ← check "L/R buttons map"
    ((setButtons sK0 0x400).key.input == 0x1FF
      && (setButtons sK0 0x800).key.input == 0x2FF)
  ok := c99d && ok
  -- release → no new IRQ (IF stays as acked below)
  let sK4 := memWrite16 sK3 0x04000202 0x1000
  let sK5 := setButtons sK4 0
  let c99c ← check "KEYCNT quiet when released"
    (sK5.irq.if_ == 0 && sK5.key.input == 0x3FF)
  ok := c99c && ok
  -- ---- Phase 10: color effects (alpha + brightness) ----
  -- alpha: BG0 red over BG2 blue, EVA=EVB=8 → (127,0,127)
  let sF := blit s0 0x05000000 [0, 0, 0x1F, 0, 0xFF, 0x7F, 0, 0x7C]
  let sF := blit sF 0x06000000 (List.replicate 32 0x11)
  let sF := blit sF 0x06000020 (List.replicate 32 0x33)
  let sF := blit sF 0x06000800 [0, 0]
  let sF := blit sF 0x06001000 [1, 0]
  let sF := memWrite16 (memWrite16 sF 0x04000000 0x0500) 0x04000008 0x0100
  let sF := memWrite16 sF 0x0400000C 0x0201
  let sF := memWrite16 (memWrite16 sF 0x04000050 0x1441) 0x04000052 0x0808
  let c102 ← check "alpha red over blue"
    ((renderFrame sF).fb.getD 0 0 == 0xFF7F007F)
  ok := c102 && ok
  -- brightness increase on BG0 red with EVY 8 → (255,127,127)
  let sB := memWrite16 (memWrite16 sF 0x04000050 0x0081) 0x04000054 8
  let c103 ← check "brightness increase"
    ((renderFrame sB).fb.getD 0 0 == 0xFFFF7F7F)
  ok := c103 && ok
  -- semi-transparent white sprite over red BG blends without targets
  let sS := blit s0 0x05000000 [0, 0, 0x1F, 0]
  let sS := blit sS 0x05000200 [0, 0, 0, 0, 0xFF, 0x7F]
  let sS := blit sS 0x06000000 (List.replicate 32 0x11)
  let sS := blit sS 0x06000800 [0, 0]
  let sS := blit sS 0x06010000 (List.replicate 32 0x22)
  let sS := memWrite16 (memWrite16 sS 0x04000000 0x1100) 0x04000008 0x0100
  let sS := memWrite16 (memWrite16 sS 0x04000050 0x0100) 0x04000052 0x0808
  let sS := (List.range 127).foldl
    (fun s i => memWrite8 s (w32 (0x07000008 + 8 * i)) 160) sS
  let sS := memWrite16 sS 0x07000000 0x0400
  let c104 ← check "semi sprite blends"
    ((renderFrame sS).fb.getD 0 0 == 0xFFFF7F7F)
  ok := c104 && ok
  -- ---- Render memo (exact: miss renders, hit reuses, non-render
  -- ---- registers don't disturb the key, VRAM writes miss) ----
  -- mode 3 scene: VRAM zero → black origin pixel
  let g0 := memWrite16 (loadROM testROM) 0x04000000 0x0003
  let (g1, m1) := memoRenderFrame g0 {}
  let c113 ← check "memo miss renders (px0 black)"
    (m1.valid && g1.fb.getD 0 0xFFFFFFFF == 0xFF000000)
  ok := c113 && ok
  let (g2, m2) := memoRenderFrame g1 m1
  let c114 ← check "memo hit reuses fb"
    (m2.valid && g2.fb == g1.fb)
  ok := c114 && ok
  -- VCOUNT/dots/frame advance: pixels unaffected → still a hit
  let gV := { g1 with ppu :=
    { g1.ppu with vcount := 100, dots := 999, frame := g1.ppu.frame + 5 } }
  let (g3, _) := memoRenderFrame gV m1
  let c115 ← check "memo hit across VCOUNT advance"
    (g3.fb == g1.fb)
  ok := c115 && ok
  -- VRAM write at the origin pixel: miss, re-rendered red
  let gW := memWrite8 (memWrite8 g1 (w32 0x06000000) 0x1F) (w32 0x06000001) 0x00
  let (g4, m4) := memoRenderFrame gW m2
  let c116 ← check "memo miss on VRAM write (px0 red)"
    (m4.valid && g4.fb.getD 0 0xFFFFFFFF == 0xFFFF0000)
  ok := c116 && ok
  -- ---- 8bpp 2D-mapping row stride (GBATEK/Tonc: tile rows stride 32
  -- ---- IDs for both depths; col strides 1 (4bpp) / 2 (8bpp)) ----
  -- 16x16 8bpp square at (4,4), tile 0, 2D mapping: row 0 = tiles
  -- 0,2; row 1 = tiles 32,34 (bytes 0, 64, 1024, 1088 past OBJ base).
  let e8 := memWrite16 (loadROM testROM) 0x04000000 0x1000
  let e8 := blit e8 0x05000000 [0, 0]
  let e8 := blit e8 0x05000200 [0, 0, 0x1F, 0, 0xE0, 0x03, 0, 0x7C, 0xFF, 0x7F]
  let e8 := memWrite8 e8 (w32 0x06010000) 1
  let e8 := memWrite8 e8 (w32 0x06010040) 2
  let e8 := memWrite8 e8 (w32 0x06010400) 3
  let e8 := memWrite8 e8 (w32 0x06010440) 4
  let e8 := blit e8 0x07000000 [0x04, 0x20, 0x04, 0x40, 0, 0, 0, 0]
  let e8 := (List.range 127).foldl
    (fun s i => memWrite8 s (w32 (0x07000008 + 8 * i)) 160) e8
  let f8 := (renderFrame e8).fb
  let c117 ← check "8bpp 2D top-left red"
    (f8.getD (4 + 4 * 240) 0 == 0xFFFF0000)
  ok := c117 && ok
  let c118 ← check "8bpp 2D top-right green"
    (f8.getD (12 + 4 * 240) 0 == 0xFF00FF00)
  ok := c118 && ok
  let c119 ← check "8bpp 2D bottom-left blue (row stride 32)"
    (f8.getD (4 + 12 * 240) 0 == 0xFF0000FF)
  ok := c119 && ok
  let c120 ← check "8bpp 2D bottom-right white"
    (f8.getD (12 + 12 * 240) 0 == 0xFFFFFFFF)
  ok := c120 && ok
  -- 1D mapping 8bpp 16x16: tiles pack consecutively (row 1 = IDs 4,6
  -- → bytes 128, 192 past OBJ base); DISPCNT.6 set.
  let e1 := memWrite16 (loadROM testROM) 0x04000000 0x1040
  let e1 := blit e1 0x05000000 [0, 0]
  let e1 := blit e1 0x05000200 [0, 0, 0x1F, 0, 0xE0, 0x03, 0, 0x7C, 0xFF, 0x7F]
  let e1 := memWrite8 e1 (w32 0x06010000) 1
  let e1 := memWrite8 e1 (w32 0x06010040) 2
  let e1 := memWrite8 e1 (w32 0x06010080) 3
  let e1 := memWrite8 e1 (w32 0x060100C0) 4
  let e1 := blit e1 0x07000000 [0x04, 0x20, 0x04, 0x40, 0, 0, 0, 0]
  let e1 := (List.range 127).foldl
    (fun s i => memWrite8 s (w32 (0x07000008 + 8 * i)) 160) e1
  let f1 := (renderFrame e1).fb
  let c121 ← check "8bpp 1D bottom-left blue"
    (f1.getD (4 + 12 * 240) 0 == 0xFF0000FF)
  ok := c121 && ok
  let c122 ← check "8bpp 1D bottom-right white"
    (f1.getD (12 + 12 * 240) 0 == 0xFFFFFFFF)
  ok := c122 && ok
  -- hflip mirrors the 8bpp 2D sprite: left/right quadrants swap.
  -- (full-tile fills: mirroring addresses tile interiors, not origins)
  let eH := memWrite16 (loadROM testROM) 0x04000000 0x1000
  let eH := blit eH 0x05000000 [0, 0]
  let eH := blit eH 0x05000200 [0, 0, 0x1F, 0, 0xE0, 0x03, 0, 0x7C, 0xFF, 0x7F]
  let eH := blit eH 0x06010000 (List.replicate 64 1 ++ List.replicate 64 2)
  let eH := blit eH 0x06010400 (List.replicate 64 3 ++ List.replicate 64 4)
  let eH := blit eH 0x07000000 [0x04, 0x20, 0x04, 0x50, 0, 0, 0, 0]
  let eH := (List.range 127).foldl
    (fun s i => memWrite8 s (w32 (0x07000008 + 8 * i)) 160) eH
  let fH := (renderFrame eH).fb
  let c123 ← check "8bpp hflip swaps left/right"
    (fH.getD (4 + 4 * 240) 0 == 0xFF00FF00
      && fH.getD (12 + 4 * 240) 0 == 0xFFFF0000
      && fH.getD (4 + 12 * 240) 0 == 0xFFFFFFFF
      && fH.getD (12 + 12 * 240) 0 == 0xFF0000FF)
  ok := c123 && ok
  -- Y-wraparound: 16x16 4bpp 1D sprite at Y=250 shows sprite rows
  -- 6..15 at screen rows 0..9 (rows 250..255, then 0..9).
  let eW := memWrite16 (loadROM testROM) 0x04000000 0x1040
  let eW := blit eW 0x05000000 [0, 0]
  let eW := blit eW 0x05000200 [0, 0, 0x1F, 0, 0xE0, 0x03, 0, 0x7C, 0xFF, 0x7F]
  let eW := blit eW 0x06010000
    (List.replicate 32 1 ++ List.replicate 32 2 ++ List.replicate 32 3
      ++ List.replicate 32 4)
  let eW := blit eW 0x07000000 [0xFA, 0, 0x04, 0x40, 0, 0, 0, 0]
  let eW := (List.range 127).foldl
    (fun s i => memWrite8 s (w32 (0x07000008 + 8 * i)) 160) eW
  let fW := (renderFrame eW).fb
  let c124 ← check "wrap row 0 shows sprite row 6 (red)"
    (fW.getD (4 + 0 * 240) 0 == 0xFFFF0000)
  ok := c124 && ok
  let c125 ← check "wrap row 8 shows sprite row 14 (white)"
    (fW.getD (12 + 8 * 240) 0 == 0xFFFFFFFF)
  ok := c125 && ok
  let c126 ← check "wrap gap row 100 is backdrop"
    (fW.getD (4 + 100 * 240) 0 == 0xFF000000)
  ok := c126 && ok
  -- ---- Sound: PSG tone, mixer, envelope, FIFO, DMA, wave, length ----
  -- CH1 duty 2, vol 15, freq 0x600, trigger; ch1 L+R, max vols, full, on.
  let aA := memWrite16 (loadROM testROM) 0x04000062 0xF080
  let aA := memWrite16 aA 0x04000064 0x8600
  let aA := memWrite16 aA 0x04000080 0x1177
  let aA := memWrite16 aA 0x04000082 0x0002
  let aA := memWrite16 aA 0x04000084 0x0080
  let c127 ← check "SOUNDCNT_X status (ch1 + master)"
    (memRead16 aA 0x04000084 == 0xF1)
  ok := c127 && ok
  -- white-box mixer levels (duty phase 0 → 15, phase 4 → 0)
  let m0ch : GB.PulseCh :=
    { enable := true, dac := true, duty := 2, phase := 0, vol := 15 }
  let m0 : AgbApu :=
    { ch1 := m0ch, cntL := 0x1177, cntH := 0x0002, cntX := 0x0080 }
  let c128 ← check "mixer ch1 high level"
    (apuMix m0 == (3584, 3584))
  ok := c128 && ok
  let c129 ← check "mixer ch1 low level"
    (apuMix { m0 with ch1 := { m0.ch1 with phase := 4 } }
      == (-4096, -4096))
  ok := c129 && ok
  -- integration: triggered tone emits varied samples
  let aR := runUntilCycles aA 100000
  let (_, snd) := apuDrain aR.apu
  let nS := snd.size / 4
  let mm := (List.range nS).foldl (fun (acc : Int × Int) i =>
    let lo := (bget snd (i * 4)).toNat
    let hi := (bget snd (i * 4 + 1)).toNat
    let v : Int :=
      if hi >= 128 then (lo : Int) + (hi : Int) * 256 - 65536
      else (lo : Int) + (hi : Int) * 256
    ((if v < acc.1 then v else acc.1), (if v > acc.2 then v else acc.2))) (0, 0)
  let c130 ← check "tone emits varied samples"
    (decide (nS >= 150) && decide (mm.1 < mm.2))
  ok := c130 && ok
  -- envelope ticks down (reused DMG logic, white-box)
  let eC : GB.PulseCh :=
    { initVol := 5, vol := 5, envDir := false, envPeriod := 1, envTimer := 0 }
  let c131 ← check "envelope decays"
    ((GB.PulseCh.envTick (GB.PulseCh.envTick eC)).vol == 4)
  ok := c131 && ok
  -- FIFO A on timer0: pushed +64s drain through the mixer
  let f0 := memWrite16 (loadROM testROM) 0x04000100 0xFF00
  let f0 := memWrite16 f0 0x04000102 0x0080
  let f0 := memWrite16 f0 0x04000082 0x0306
  let f0 := memWrite16 f0 0x04000084 0x0080
  let f0 := memWrite32 f0 0x040000A0 0x40404040
  let f0 := memWrite32 f0 0x040000A0 0x40404040
  let f0 := memWrite32 f0 0x040000A0 0x40404040
  let f0 := memWrite32 f0 0x040000A0 0x40404040
  let f0 := memWrite32 f0 0x040000A0 0x40404040
  let f0 := memWrite32 f0 0x040000A0 0x40404040
  let f0 := memWrite32 f0 0x040000A0 0x40404040
  let f0 := memWrite32 f0 0x040000A0 0x40404040
  let f1 := runUntilCycles f0 9000
  let (_, sndF) := apuDrain f1.apu
  let nF := sndF.size / 4
  let mxF := (List.range nF).foldl (fun (acc : Int) i =>
    let lo := (bget sndF (i * 4)).toNat
    let hi := (bget sndF (i * 4 + 1)).toNat
    let v : Int :=
      if hi >= 128 then (lo : Int) + (hi : Int) * 256 - 65536
      else (lo : Int) + (hi : Int) * 256
    if v > acc then v else acc) 0
  let c132 ← check "FIFO A plays positive, drains"
    (decide (mxF > 0) && f1.apu.fifoA.data.size == 0)
  ok := c132 && ok
  -- sound DMA refill: one timer0 overflow → 16 bytes, SAD +16, kept live
  let d0 := blit (loadROM testROM) 0x02000000 (List.replicate 16 0x7F)
  let d0 := memWrite32 d0 0x040000BC 0x02000000
  let d0 := memWrite32 d0 0x040000C0 0x040000A0
  let d0 := memWrite16 d0 0x040000C4 0
  let d0 := memWrite16 d0 0x040000C6 0xB640
  let d0 := memWrite16 d0 0x04000100 0xFF00
  let d0 := memWrite16 d0 0x04000102 0x0080
  let d0 := memWrite16 d0 0x04000082 0x0302
  let d0 := memWrite16 d0 0x04000084 0x0080
  let d1 := runUntilCycles d0 300
  let c133 ← check "sound DMA refills FIFO"
    ((d1.dma.ch.getD 1 {}).sad == 0x02000010
      && d1.apu.fifoA.data.size == 16
      && ((((d1.dma.ch.getD 1 {}).cnt_h >>> 15) &&& 1) == 1)
      && d1.apu.fifoA.out == 0)
  ok := c133 && ok
  -- wave channel end-to-end (banked RAM, square-ish wave, varying out)
  let w0 := memWrite16 (loadROM testROM) 0x04000070 0x00C0
  let w0 := blit w0 0x04000090
    (List.replicate 8 0xFF ++ List.replicate 8 0x00)
  let w0 := memWrite16 w0 0x04000070 0x0080
  let w0 := memWrite16 w0 0x04000072 0x2000
  let w0 := memWrite16 w0 0x04000074 0x8700
  let w0 := memWrite16 w0 0x04000080 0x4477
  let w0 := memWrite16 w0 0x04000082 0x0002
  let w0 := memWrite16 w0 0x04000084 0x0080
  let w1 := runUntilCycles w0 100000
  let (_, sndW) := apuDrain w1.apu
  let nW := sndW.size / 4
  let nzW := (List.range nW).foldl (fun (acc : Nat × Int × Int) i =>
    let lo := (bget sndW (i * 4)).toNat
    let hi := (bget sndW (i * 4 + 1)).toNat
    let v : Int :=
      if hi >= 128 then (lo : Int) + (hi : Int) * 256 - 65536
      else (lo : Int) + (hi : Int) * 256
    ((if v != 0 then acc.1 + 1 else acc.1),
      (if v < acc.2.1 then v else acc.2.1),
      (if v > acc.2.2 then v else acc.2.2))) (0, 0, 0)
  let c134 ← check "wave channel varies"
    (decide (nzW.1 > 50) && decide (nzW.2.1 < nzW.2.2))
  ok := c134 && ok
  -- length expiry disables the channel (len 1 → X status bit clears)
  let l0 := memWrite16 (loadROM testROM) 0x04000062 0xF0BF
  let l0 := memWrite16 l0 0x04000064 0xC600
  let l0 := memWrite16 l0 0x04000080 0x1177
  let l0 := memWrite16 l0 0x04000082 0x0002
  let l0 := memWrite16 l0 0x04000084 0x0080
  let l1 := runUntilCycles l0 40000
  let c135 ← check "length expiry disables ch1"
    (((memRead16 l1 0x04000084).toNat &&& 1) == 0)
  ok := c135 && ok
  -- BIOS RegisterRamReset sound bit clears the APU
  let sB := biosRegReset aA 0x40
  let c136 ← check "RegisterRamReset clears sound"
    (sB.apu.cntX == 0 && !sB.apu.ch1.enable
      && sB.apu.fifoA.data.size == 0)
  ok := c136 && ok
  -- sound DMA data path (exact bytes): ramp 1..64 in EWRAM, DMA1
  -- one-shot to FIFO A, timer0 overflows every 512 cycles.
  let r0 := blit (loadROM testROM) 0x02000100
    ((List.range 64).map (· + 1))
  let r0 := memWrite32 r0 0x040000BC 0x02000100
  let r0 := memWrite32 r0 0x040000C0 0x040000A0
  let r0 := memWrite16 r0 0x040000C4 0
  let r0 := memWrite16 r0 0x040000C6 0xB600
  let r0 := memWrite16 r0 0x04000100 0xFE00
  let r0 := memWrite16 r0 0x04000102 0x0080
  let r0 := memWrite16 r0 0x04000082 0x0B04
  let r0 := memWrite16 r0 0x04000084 0x0080
  let r1 := runUntilCycles r0 512
  let c137 ← check "DMA refill brings exact bytes"
    (r1.apu.fifoA.data.toList.map (·.toNat) == (List.range 16).map (· + 1)
      && (r1.dma.ch.getD 1 {}).sad == 0x02000110
      && (((r1.dma.ch.getD 1 {}).cnt_h >>> 15) &&& 1) == 1
      && r1.apu.fifoA.out == 0)
  ok := c137 && ok
  let r2 := runUntilCycles r1 512
  let c138 ← check "FIFO pop order, repeat refills"
    (r2.apu.fifoA.out == 1 && r2.apu.fifoA.data.size == 31
      && (r2.dma.ch.getD 1 {}).sad == 0x02000120)
  ok := c138 && ok
  -- white-box FIFO→mixer scaling (out 64, full vol, L only)
  let mF : AgbApu :=
    { fifoA := { data := #[], out := 64 }, cntH := 0x0306,
      cntL := 0, cntX := 0x0080 }
  let c139 ← check "FIFO mixer scaling"
    (apuMix mF == (4096, 4096))
  ok := c139 && ok
  ok := c138 && ok
  -- save-string autodetect on marker ROMs
  let mkRom (s : String) : ByteArray :=
    ByteArray.mk (Array.mk ((markerBytes s).map (fun n => w8 n)))
  let c98 ← check "detect kinds"
    (detectSaveKind (mkRom "FLASH1M_V102") == .flash128
      && detectSaveKind (mkRom "FLASH512_V130") == .flash64
      && detectSaveKind (mkRom "EEPROM_V126") == .eeprom64k
      && detectSaveKind (mkRom "EEPROM_V120") == .eeprom4k
      && detectSaveKind (mkRom "SRAM_V112") == .sram
      && detectSaveKind ByteArray.empty == .sram)
  ok := c98 && ok
  if ok then IO.println "[agb-test] ALL PASS" else IO.Process.exit 1
