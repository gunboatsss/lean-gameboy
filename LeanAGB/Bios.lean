import LeanAGB.Basic

/- LeanAGB.Bios — HLE SWI dispatch table (no bios.bin needed).
   Phase 3: + ArcTan/ArcTan2 (0x09/0x0A), BgAffineSet/ObjAffineSet
   (0x0E/0x0F), BitUnPack (0x10), LZ77 (0x11/0x12), Huff (0x13),
   RL (0x14/0x15), Diff filters (0x16/0x17/0x18). Sound SWIs still
   take the real SVC vector (no APU yet). -/
namespace AGB
def SWI_SOFTRESET : Nat := 0x00
def SWI_REGRAMRESET : Nat := 0x01
def SWI_HALT : Nat := 0x02
def SWI_STOP : Nat := 0x03
def SWI_INTRWAIT : Nat := 0x04
def SWI_VBLANKWAIT : Nat := 0x05
def SWI_DIV : Nat := 0x06
def SWI_DIVARM : Nat := 0x07
def SWI_SQRT : Nat := 0x08
def SWI_ARCTAN : Nat := 0x09
def SWI_ARCTAN2 : Nat := 0x0A
def SWI_CPUSET : Nat := 0x0B
def SWI_CPUFASTSET : Nat := 0x0C
def SWI_BGAFFINE : Nat := 0x0E
def SWI_OBJAFFINE : Nat := 0x0F
def SWI_BITUNPACK : Nat := 0x10
def SWI_LZ77WRAM : Nat := 0x11
def SWI_LZ77VRAM : Nat := 0x12
def SWI_HUFF : Nat := 0x13
def SWI_RLWRAM : Nat := 0x14
def SWI_RLVRAM : Nat := 0x15
def SWI_DIFF8W : Nat := 0x16
def SWI_DIFF8V : Nat := 0x17
def SWI_DIFF16 : Nat := 0x18

-- ── Minimal BIOS stub (GBATEK "BIOS Interrupt handling") ──
-- Only the IRQ path is materialized: vector 0x18 branches to a
-- verbatim copy of the BIOS dispatcher (STMFD/MOV/ADD/LDR/LDMFD/SUBS)
-- which pushes to SP_irq, calls [0x03007FFC] in ARM state with
-- LR = 0x138, then restores and returns via SUBS pc,lr,#4.
-- Reset/SWI vectors stay zero (direct boot + HLE never land there).

/-- Hand-assembled IRQ dispatcher (verified by decode pins in proofs). -/
def agbBiosStub : List (Nat × Nat) :=
  [(0x18, 0xEA000042),    -- b 0x128
   (0x128, 0xE92D500F),   -- stmfd r13!, {r0-r3, r12, r14}
   (0x12C, 0xE3A00301),   -- mov r0, #0x04000000 (ROR(1,6), not ROR(1,26))
   (0x130, 0xE28FE000),   -- add r14, r15, #0  (ret = 0x138)
   (0x134, 0xE510F004),   -- ldr r15, [r0, #-4]  (jump [0x03007FFC])
   (0x138, 0xE8BD500F),   -- ldmfd r13!, {r0-r3, r12, r14}
   (0x13C, 0xE25EF004)]   -- subs r15, r14, #4

def agbBios : ByteArray :=
  let blank := ByteArray.mk (Array.replicate 0x140 (0 : UInt8))
  agbBiosStub.foldl (fun b (off, w) => bset32LE b off (w32 w)) blank

end AGB
