/-
  LeanAGB.Proofs.Exec — executor contracts: exact per-instruction cycle
  costs, cycle preservation (per-arm + master), per-step monotonicity,
  and bounded reachability on a concrete program.
-/
import LeanAGB.Proofs.Bus
import LeanAGB.Proofs.Decode
import LeanAGB.Emu

namespace AGB

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

-- ── HLE preserves cycles ──

theorem biosSoftReset_cycles (s : AGBState) :
    (biosSoftReset s).cycles = s.cycles := by
  unfold biosSoftReset
  rfl

theorem biosRREwram_cycles (s : AGBState) (flags : UInt32) :
    (biosRREwram s flags).cycles = s.cycles := by
  unfold biosRREwram
  split <;> rfl

theorem biosRRIwram_cycles (s : AGBState) (flags : UInt32) :
    (biosRRIwram s flags).cycles = s.cycles := by
  unfold biosRRIwram
  split <;> rfl

theorem biosRRPal_cycles (s : AGBState) (flags : UInt32) :
    (biosRRPal s flags).cycles = s.cycles := by
  unfold biosRRPal
  split <;> rfl

theorem biosRRVram_cycles (s : AGBState) (flags : UInt32) :
    (biosRRVram s flags).cycles = s.cycles := by
  unfold biosRRVram
  split <;> rfl

theorem biosRROam_cycles (s : AGBState) (flags : UInt32) :
    (biosRROam s flags).cycles = s.cycles := by
  unfold biosRROam
  split <;> rfl

theorem biosRRSnd_cycles (s : AGBState) (flags : UInt32) :
    (biosRRSnd s flags).cycles = s.cycles := by
  unfold biosRRSnd
  split <;> rfl

theorem biosRRTimers_cycles (s : AGBState) (flags : UInt32) :
    (biosRRTimers s flags).cycles = s.cycles := by
  unfold biosRRTimers
  simp only []
  repeat (first | split | rfl)

theorem biosRegReset_cycles (s : AGBState) (flags : UInt32) :
    (biosRegReset s flags).cycles = s.cycles := by
  unfold biosRegReset
  simp only []
  rw [biosRRTimers_cycles, biosRRSnd_cycles, biosRROam_cycles,
    biosRRVram_cycles, biosRRPal_cycles, biosRRIwram_cycles,
    biosRREwram_cycles]

theorem biosDiv_cycles (s : AGBState) (num den : UInt32) :
    (biosDiv s num den).cycles = s.cycles := by
  unfold biosDiv
  simp only []
  repeat (first | split | rfl)

-- ── Phase-3 loop preservation (all write via dmaWrite + live reads) ──

theorem writeS16_cycles (s : AGBState) (addr : UInt32) (v : Int) :
    (writeS16 s addr v).cycles = s.cycles := by
  simp [writeS16, dmaWrite16_cycles]

theorem writeS16_regs (s : AGBState) (addr : UInt32) (v : Int) :
    (writeS16 s addr v).regs = s.regs := by
  simp [writeS16, dmaWrite16_regs]

theorem writeS16_rom (s : AGBState) (addr : UInt32) (v : Int) :
    (writeS16 s addr v).rom = s.rom := by
  simp [writeS16, dmaWrite16_rom]

theorem writeS32_cycles (s : AGBState) (addr : UInt32) (v : Int) :
    (writeS32 s addr v).cycles = s.cycles := by
  simp [writeS32, dmaWrite32_cycles]

theorem writeS32_regs (s : AGBState) (addr : UInt32) (v : Int) :
    (writeS32 s addr v).regs = s.regs := by
  simp [writeS32, dmaWrite32_regs]

theorem writeS32_rom (s : AGBState) (addr : UInt32) (v : Int) :
    (writeS32 s addr v).rom = s.rom := by
  simp [writeS32, dmaWrite32_rom]

theorem bgAffineLoop_cycles (s : AGBState) (src dst : UInt32) (n : Nat) :
    (bgAffineLoop s src dst n).cycles = s.cycles := by
  induction n generalizing s src dst with
  | zero => rfl
  | succ n ih =>
    simp only [bgAffineLoop]
    repeat (first | simp [ih, writeS16_cycles, writeS32_cycles] | split | rfl)

theorem bgAffineLoop_regs (s : AGBState) (src dst : UInt32) (n : Nat) :
    (bgAffineLoop s src dst n).regs = s.regs := by
  induction n generalizing s src dst with
  | zero => rfl
  | succ n ih =>
    simp only [bgAffineLoop]
    repeat (first | simp [ih, writeS16_regs, writeS32_regs] | split | rfl)

theorem bgAffineLoop_rom (s : AGBState) (src dst : UInt32) (n : Nat) :
    (bgAffineLoop s src dst n).rom = s.rom := by
  induction n generalizing s src dst with
  | zero => rfl
  | succ n ih =>
    simp only [bgAffineLoop]
    repeat (first | simp [ih, writeS16_rom, writeS32_rom] | split | rfl)

theorem objAffineLoop_cycles (s : AGBState) (src dst : UInt32) (n diff : Nat) :
    (objAffineLoop s src dst n diff).cycles = s.cycles := by
  induction n generalizing s src dst with
  | zero => rfl
  | succ n ih =>
    simp only [objAffineLoop]
    repeat (first | simp [ih, writeS16_cycles] | split | rfl)

theorem objAffineLoop_regs (s : AGBState) (src dst : UInt32) (n diff : Nat) :
    (objAffineLoop s src dst n diff).regs = s.regs := by
  induction n generalizing s src dst with
  | zero => rfl
  | succ n ih =>
    simp only [objAffineLoop]
    repeat (first | simp [ih, writeS16_regs] | split | rfl)

theorem objAffineLoop_rom (s : AGBState) (src dst : UInt32) (n diff : Nat) :
    (objAffineLoop s src dst n diff).rom = s.rom := by
  induction n generalizing s src dst with
  | zero => rfl
  | succ n ih =>
    simp only [objAffineLoop]
    repeat (first | simp [ih, writeS16_rom] | split | rfl)

theorem lzCopy_cycles (s : AGBState) (dst : UInt32) (disp len : Nat) :
    ((lzCopy s dst disp len).1).cycles = s.cycles := by
  induction len generalizing s dst with
  | zero => rfl
  | succ len ih =>
    simp only [lzCopy]
    repeat (first | simp [ih, dmaWrite8_cycles] | split | rfl)

theorem lzCopy_regs (s : AGBState) (dst : UInt32) (disp len : Nat) :
    ((lzCopy s dst disp len).1).regs = s.regs := by
  induction len generalizing s dst with
  | zero => rfl
  | succ len ih =>
    simp only [lzCopy]
    repeat (first | simp [ih, dmaWrite8_regs] | split | rfl)

theorem lzCopy_rom (s : AGBState) (dst : UInt32) (disp len : Nat) :
    ((lzCopy s dst disp len).1).rom = s.rom := by
  induction len generalizing s dst with
  | zero => rfl
  | succ len ih =>
    simp only [lzCopy]
    repeat (first | simp [ih, dmaWrite8_rom] | split | rfl)

theorem lzLoop_cycles (s : AGBState) (src dst : UInt32) (rem fb fc fuel : Nat) :
    ((lzLoop s src dst rem fb fc fuel).1).cycles = s.cycles := by
  induction fuel generalizing s src dst rem fb fc with
  | zero => rfl
  | succ fuel ih =>
    simp only [lzLoop]
    repeat (first | simp [ih, lzCopy_cycles, dmaWrite8_cycles] | split | rfl)

theorem lzLoop_regs (s : AGBState) (src dst : UInt32) (rem fb fc fuel : Nat) :
    ((lzLoop s src dst rem fb fc fuel).1).regs = s.regs := by
  induction fuel generalizing s src dst rem fb fc with
  | zero => rfl
  | succ fuel ih =>
    simp only [lzLoop]
    repeat (first | simp [ih, lzCopy_regs, dmaWrite8_regs] | split | rfl)

theorem lzLoop_rom (s : AGBState) (src dst : UInt32) (rem fb fc fuel : Nat) :
    ((lzLoop s src dst rem fb fc fuel).1).rom = s.rom := by
  induction fuel generalizing s src dst rem fb fc with
  | zero => rfl
  | succ fuel ih =>
    simp only [lzLoop]
    repeat (first | simp [ih, lzCopy_rom, dmaWrite8_rom] | split | rfl)

theorem rlFill_cycles (s : AGBState) (dst : UInt32) (v : UInt8) (n : Nat) :
    ((rlFill s dst v n).1).cycles = s.cycles := by
  induction n generalizing s dst with
  | zero => rfl
  | succ n ih =>
    simp only [rlFill]
    repeat (first | simp [ih, dmaWrite8_cycles] | split | rfl)

theorem rlFill_regs (s : AGBState) (dst : UInt32) (v : UInt8) (n : Nat) :
    ((rlFill s dst v n).1).regs = s.regs := by
  induction n generalizing s dst with
  | zero => rfl
  | succ n ih =>
    simp only [rlFill]
    repeat (first | simp [ih, dmaWrite8_regs] | split | rfl)

theorem rlFill_rom (s : AGBState) (dst : UInt32) (v : UInt8) (n : Nat) :
    ((rlFill s dst v n).1).rom = s.rom := by
  induction n generalizing s dst with
  | zero => rfl
  | succ n ih =>
    simp only [rlFill]
    repeat (first | simp [ih, dmaWrite8_rom] | split | rfl)

theorem rlCopyN_cycles (s : AGBState) (src dst : UInt32) (n : Nat) :
    ((rlCopyN s src dst n).1).cycles = s.cycles := by
  induction n generalizing s src dst with
  | zero => rfl
  | succ n ih =>
    simp only [rlCopyN]
    repeat (first | simp [ih, dmaWrite8_cycles] | split | rfl)

theorem rlCopyN_regs (s : AGBState) (src dst : UInt32) (n : Nat) :
    ((rlCopyN s src dst n).1).regs = s.regs := by
  induction n generalizing s src dst with
  | zero => rfl
  | succ n ih =>
    simp only [rlCopyN]
    repeat (first | simp [ih, dmaWrite8_regs] | split | rfl)

theorem rlCopyN_rom (s : AGBState) (src dst : UInt32) (n : Nat) :
    ((rlCopyN s src dst n).1).rom = s.rom := by
  induction n generalizing s src dst with
  | zero => rfl
  | succ n ih =>
    simp only [rlCopyN]
    repeat (first | simp [ih, dmaWrite8_rom] | split | rfl)

theorem rlLoop_cycles (s : AGBState) (src dst : UInt32) (rem fuel : Nat) :
    ((rlLoop s src dst rem fuel).1).cycles = s.cycles := by
  induction fuel generalizing s src dst rem with
  | zero => rfl
  | succ fuel ih =>
    simp only [rlLoop]
    repeat (first | simp [ih, rlFill_cycles, rlCopyN_cycles] | split | rfl)

theorem rlLoop_regs (s : AGBState) (src dst : UInt32) (rem fuel : Nat) :
    ((rlLoop s src dst rem fuel).1).regs = s.regs := by
  induction fuel generalizing s src dst rem with
  | zero => rfl
  | succ fuel ih =>
    simp only [rlLoop]
    repeat (first | simp [ih, rlFill_regs, rlCopyN_regs] | split | rfl)

theorem rlLoop_rom (s : AGBState) (src dst : UInt32) (rem fuel : Nat) :
    ((rlLoop s src dst rem fuel).1).rom = s.rom := by
  induction fuel generalizing s src dst rem with
  | zero => rfl
  | succ fuel ih =>
    simp only [rlLoop]
    repeat (first | simp [ih, rlFill_rom, rlCopyN_rom] | split | rfl)

theorem rlPadB_cycles (s : AGBState) (dst : UInt32) (n : Nat) :
    ((rlPadB s dst n).1).cycles = s.cycles := by
  induction n generalizing s dst with
  | zero => rfl
  | succ n ih =>
    simp only [rlPadB]
    repeat (first | simp [ih, dmaWrite8_cycles] | split | rfl)

theorem rlPadB_regs (s : AGBState) (dst : UInt32) (n : Nat) :
    ((rlPadB s dst n).1).regs = s.regs := by
  induction n generalizing s dst with
  | zero => rfl
  | succ n ih =>
    simp only [rlPadB]
    repeat (first | simp [ih, dmaWrite8_regs] | split | rfl)

theorem rlPadB_rom (s : AGBState) (dst : UInt32) (n : Nat) :
    ((rlPadB s dst n).1).rom = s.rom := by
  induction n generalizing s dst with
  | zero => rfl
  | succ n ih =>
    simp only [rlPadB]
    repeat (first | simp [ih, dmaWrite8_rom] | split | rfl)

theorem rlPadW_cycles (s : AGBState) (dst : UInt32) (n : Nat) :
    ((rlPadW s dst n).1).cycles = s.cycles := by
  induction n generalizing s dst with
  | zero => rfl
  | succ n ih =>
    simp only [rlPadW]
    repeat (first | simp [ih, dmaWrite16_cycles] | split | rfl)

theorem rlPadW_regs (s : AGBState) (dst : UInt32) (n : Nat) :
    ((rlPadW s dst n).1).regs = s.regs := by
  induction n generalizing s dst with
  | zero => rfl
  | succ n ih =>
    simp only [rlPadW]
    repeat (first | simp [ih, dmaWrite16_regs] | split | rfl)

theorem rlPadW_rom (s : AGBState) (dst : UInt32) (n : Nat) :
    ((rlPadW s dst n).1).rom = s.rom := by
  induction n generalizing s dst with
  | zero => rfl
  | succ n ih =>
    simp only [rlPadW]
    repeat (first | simp [ih, dmaWrite16_rom] | split | rfl)

theorem huffNextBit_cycles (s : AGBState) (st : HuffSt) :
    ((huffNextBit s st).1).cycles = s.cycles := by
  unfold huffNextBit
  simp only []
  repeat (first | split | rfl)

theorem huffNextBit_regs (s : AGBState) (st : HuffSt) :
    ((huffNextBit s st).1).regs = s.regs := by
  unfold huffNextBit
  simp only []
  repeat (first | split | rfl)

theorem huffNextBit_rom (s : AGBState) (st : HuffSt) :
    ((huffNextBit s st).1).rom = s.rom := by
  unfold huffNextBit
  simp only []
  repeat (first | split | rfl)

theorem huffWalk_cycles (s : AGBState) (st : HuffSt) (fuel : Nat) :
    ((huffWalk s st fuel).1).cycles = s.cycles := by
  induction fuel generalizing s st with
  | zero => rfl
  | succ fuel ih =>
    simp only [huffWalk]
    repeat (first | simp [ih, huffNextBit_cycles] | split | rfl)

theorem huffWalk_regs (s : AGBState) (st : HuffSt) (fuel : Nat) :
    ((huffWalk s st fuel).1).regs = s.regs := by
  induction fuel generalizing s st with
  | zero => rfl
  | succ fuel ih =>
    simp only [huffWalk]
    repeat (first | simp [ih, huffNextBit_regs] | split | rfl)

theorem huffWalk_rom (s : AGBState) (st : HuffSt) (fuel : Nat) :
    ((huffWalk s st fuel).1).rom = s.rom := by
  induction fuel generalizing s st with
  | zero => rfl
  | succ fuel ih =>
    simp only [huffWalk]
    repeat (first | simp [ih, huffNextBit_rom] | split | rfl)

theorem huffLoop_cycles (s : AGBState) (dst : UInt32) (rem cur fill bits : Nat)
    (st : HuffSt) (maxD fuel : Nat) :
    ((huffLoop s dst rem cur fill bits st maxD fuel).1).cycles = s.cycles := by
  induction fuel generalizing s dst rem cur fill st with
  | zero => rfl
  | succ fuel ih =>
    simp only [huffLoop]
    repeat (first | simp [ih, huffWalk_cycles, dmaWrite8_cycles] | split | rfl)

theorem huffLoop_regs (s : AGBState) (dst : UInt32) (rem cur fill bits : Nat)
    (st : HuffSt) (maxD fuel : Nat) :
    ((huffLoop s dst rem cur fill bits st maxD fuel).1).regs = s.regs := by
  induction fuel generalizing s dst rem cur fill st with
  | zero => rfl
  | succ fuel ih =>
    simp only [huffLoop]
    repeat (first | simp [ih, huffWalk_regs, dmaWrite8_regs] | split | rfl)

theorem huffLoop_rom (s : AGBState) (dst : UInt32) (rem cur fill bits : Nat)
    (st : HuffSt) (maxD fuel : Nat) :
    ((huffLoop s dst rem cur fill bits st maxD fuel).1).rom = s.rom := by
  induction fuel generalizing s dst rem cur fill st with
  | zero => rfl
  | succ fuel ih =>
    simp only [huffLoop]
    repeat (first | simp [ih, huffWalk_rom, dmaWrite8_rom] | split | rfl)

theorem bitLoop_cycles (s : AGBState) (src dst : UInt32) (inB bitsLeft srcLen : Nat)
    (out outBits srcW dstW : Nat) (off : Nat) (addZero : Bool) (fuel : Nat) :
    ((bitLoop s src dst inB bitsLeft srcLen out outBits srcW dstW off addZero fuel).1).cycles
      = s.cycles := by
  induction fuel generalizing s src dst inB bitsLeft srcLen out outBits with
  | zero => rfl
  | succ fuel ih =>
    simp only [bitLoop]
    repeat (first | simp [ih, dmaWrite8_cycles] | split | rfl)

theorem bitLoop_regs (s : AGBState) (src dst : UInt32) (inB bitsLeft srcLen : Nat)
    (out outBits srcW dstW : Nat) (off : Nat) (addZero : Bool) (fuel : Nat) :
    ((bitLoop s src dst inB bitsLeft srcLen out outBits srcW dstW off addZero fuel).1).regs
      = s.regs := by
  induction fuel generalizing s src dst inB bitsLeft srcLen out outBits with
  | zero => rfl
  | succ fuel ih =>
    simp only [bitLoop]
    repeat (first | simp [ih, dmaWrite8_regs] | split | rfl)

theorem bitLoop_rom (s : AGBState) (src dst : UInt32) (inB bitsLeft srcLen : Nat)
    (out outBits srcW dstW : Nat) (off : Nat) (addZero : Bool) (fuel : Nat) :
    ((bitLoop s src dst inB bitsLeft srcLen out outBits srcW dstW off addZero fuel).1).rom
      = s.rom := by
  induction fuel generalizing s src dst inB bitsLeft srcLen out outBits with
  | zero => rfl
  | succ fuel ih =>
    simp only [bitLoop]
    repeat (first | simp [ih, dmaWrite8_rom] | split | rfl)

theorem diffLoop_cycles (s : AGBState) (src dst : UInt32) (rem acc : Nat)
    (wide : Bool) (fuel : Nat) :
    ((diffLoop s src dst rem acc wide fuel).1).cycles = s.cycles := by
  induction fuel generalizing s src dst rem acc wide with
  | zero => rfl
  | succ fuel ih =>
    simp only [diffLoop]
    repeat (first | simp [ih, dmaWrite16_cycles, dmaWrite8_cycles] | split | rfl)

theorem diffLoop_regs (s : AGBState) (src dst : UInt32) (rem acc : Nat)
    (wide : Bool) (fuel : Nat) :
    ((diffLoop s src dst rem acc wide fuel).1).regs = s.regs := by
  induction fuel generalizing s src dst rem acc wide with
  | zero => rfl
  | succ fuel ih =>
    simp only [diffLoop]
    repeat (first | simp [ih, dmaWrite16_regs, dmaWrite8_regs] | split | rfl)

theorem diffLoop_rom (s : AGBState) (src dst : UInt32) (rem acc : Nat)
    (wide : Bool) (fuel : Nat) :
    ((diffLoop s src dst rem acc wide fuel).1).rom = s.rom := by
  induction fuel generalizing s src dst rem acc wide with
  | zero => rfl
  | succ fuel ih =>
    simp only [diffLoop]
    repeat (first | simp [ih, dmaWrite16_rom, dmaWrite8_rom] | split | rfl)

theorem hleSwiCpuSet_cycles (s : AGBState) :
    (hleSwiCpuSet s).cycles = s.cycles := by
  unfold hleSwiCpuSet
  simp only []
  repeat (first | simp [dmaRun_cycles] | split | rfl)

theorem hleSwiCpuFastSet_cycles (s : AGBState) :
    (hleSwiCpuFastSet s).cycles = s.cycles := by
  unfold hleSwiCpuFastSet
  simp only []
  repeat (first | simp [dmaRun_cycles] | split | rfl)

theorem hleSwiHalt_cycles (s : AGBState) :
    (hleSwiHalt s).cycles = s.cycles := by
  rfl

theorem hleSwiVBlankWait_cycles (s : AGBState) :
    (hleSwiVBlankWait s).cycles = s.cycles := by
  rfl

theorem hleSwiSqrt_cycles (s : AGBState) :
    (hleSwiSqrt s).cycles = s.cycles := by
  rfl

theorem hleSwiIntrWait_cycles (s : AGBState) :
    ((hleSwiIntrWait s).1).cycles = s.cycles := by
  unfold hleSwiIntrWait
  simp only []
  repeat (first | split | rfl)

theorem hleSwiArcTan_cycles (s : AGBState) :
    (hleSwiArcTan s).cycles = s.cycles := by
  unfold hleSwiArcTan
  simp only []

theorem hleSwiArcTan2_cycles (s : AGBState) :
    (hleSwiArcTan2 s).cycles = s.cycles := by
  unfold hleSwiArcTan2
  simp only []
  repeat (first | split | rfl)

theorem hleSwiBgAffine_cycles (s : AGBState) :
    (hleSwiBgAffine s).cycles = s.cycles := by
  unfold hleSwiBgAffine
  repeat (first | simp [bgAffineLoop_cycles] | split | rfl)

theorem hleSwiBgAffine_regs (s : AGBState) :
    (hleSwiBgAffine s).regs = s.regs := by
  unfold hleSwiBgAffine
  repeat (first | simp [bgAffineLoop_regs] | split | rfl)

theorem hleSwiBgAffine_rom (s : AGBState) :
    (hleSwiBgAffine s).rom = s.rom := by
  unfold hleSwiBgAffine
  repeat (first | simp [bgAffineLoop_rom] | split | rfl)

theorem hleSwiObjAffine_cycles (s : AGBState) :
    (hleSwiObjAffine s).cycles = s.cycles := by
  unfold hleSwiObjAffine
  repeat (first | simp [objAffineLoop_cycles] | split | rfl)

theorem hleSwiObjAffine_regs (s : AGBState) :
    (hleSwiObjAffine s).regs = s.regs := by
  unfold hleSwiObjAffine
  repeat (first | simp [objAffineLoop_regs] | split | rfl)

theorem hleSwiObjAffine_rom (s : AGBState) :
    (hleSwiObjAffine s).rom = s.rom := by
  unfold hleSwiObjAffine
  repeat (first | simp [objAffineLoop_rom] | split | rfl)

theorem hleSwiLz_cycles (s : AGBState) :
    (hleSwiLz s).cycles = s.cycles := by
  unfold hleSwiLz
  simp only []
  repeat (first | simp [lzLoop_cycles] | split | rfl)

theorem hleSwiLz_regs (s : AGBState) :
    (hleSwiLz s).regs = s.regs := by
  unfold hleSwiLz
  simp only []
  repeat (first | simp [lzLoop_regs] | split | rfl)

theorem hleSwiLz_rom (s : AGBState) :
    (hleSwiLz s).rom = s.rom := by
  unfold hleSwiLz
  simp only []
  repeat (first | simp [lzLoop_rom] | split | rfl)

theorem hleSwiRl_cycles (s : AGBState) (wide : Bool) :
    (hleSwiRl s wide).cycles = s.cycles := by
  unfold hleSwiRl
  simp only []
  repeat (first | simp [rlLoop_cycles, rlPadB_cycles, rlPadW_cycles] | split | rfl)

theorem hleSwiRl_regs (s : AGBState) (wide : Bool) :
    (hleSwiRl s wide).regs = s.regs := by
  unfold hleSwiRl
  simp only []
  repeat (first | simp [rlLoop_regs, rlPadB_regs, rlPadW_regs] | split | rfl)

theorem hleSwiRl_rom (s : AGBState) (wide : Bool) :
    (hleSwiRl s wide).rom = s.rom := by
  unfold hleSwiRl
  simp only []
  repeat (first | simp [rlLoop_rom, rlPadB_rom, rlPadW_rom] | split | rfl)

theorem hleSwiHuff_cycles (s : AGBState) :
    (hleSwiHuff s).cycles = s.cycles := by
  unfold hleSwiHuff
  simp only []
  repeat (first | simp [huffLoop_cycles] | split | rfl)

theorem hleSwiHuff_regs (s : AGBState) :
    (hleSwiHuff s).regs = s.regs := by
  unfold hleSwiHuff
  simp only []
  repeat (first | simp [huffLoop_regs] | split | rfl)

theorem hleSwiHuff_rom (s : AGBState) :
    (hleSwiHuff s).rom = s.rom := by
  unfold hleSwiHuff
  simp only []
  repeat (first | simp [huffLoop_rom] | split | rfl)

theorem hleSwiBitUnPack_cycles (s : AGBState) :
    (hleSwiBitUnPack s).cycles = s.cycles := by
  unfold hleSwiBitUnPack
  simp only []
  repeat (first | simp [bitLoop_cycles] | split | rfl)

theorem hleSwiBitUnPack_regs (s : AGBState) :
    (hleSwiBitUnPack s).regs = s.regs := by
  unfold hleSwiBitUnPack
  simp only []
  repeat (first | simp [bitLoop_regs] | split | rfl)

theorem hleSwiBitUnPack_rom (s : AGBState) :
    (hleSwiBitUnPack s).rom = s.rom := by
  unfold hleSwiBitUnPack
  simp only []
  repeat (first | simp [bitLoop_rom] | split | rfl)

theorem hleSwiDiff_cycles (s : AGBState) (inW : Nat) :
    (hleSwiDiff s inW).cycles = s.cycles := by
  unfold hleSwiDiff
  simp only []
  repeat (first | simp [diffLoop_cycles] | split | rfl)

theorem hleSwiDiff_regs (s : AGBState) (inW : Nat) :
    (hleSwiDiff s inW).regs = s.regs := by
  unfold hleSwiDiff
  simp only []
  repeat (first | simp [diffLoop_regs] | split | rfl)

theorem hleSwiDiff_rom (s : AGBState) (inW : Nat) :
    (hleSwiDiff s inW).rom = s.rom := by
  unfold hleSwiDiff
  simp only []
  repeat (first | simp [diffLoop_rom] | split | rfl)

theorem hleSwiDecomp_cycles (s : AGBState) (imm : Nat) :
    ((hleSwiDecomp s imm).1).cycles = s.cycles := by
  unfold hleSwiDecomp
  repeat (first | simp [hleSwiBitUnPack_cycles, hleSwiLz_cycles,
    hleSwiRl_cycles, hleSwiHuff_cycles, hleSwiDiff_cycles] | split | rfl)

theorem hleSwiCopy_cycles (s : AGBState) (imm : Nat) :
    ((hleSwiCopy s imm).1).cycles = s.cycles := by
  unfold hleSwiCopy
  repeat (first | simp [hleSwiCpuSet_cycles, hleSwiCpuFastSet_cycles,
    hleSwiArcTan_cycles, hleSwiArcTan2_cycles, hleSwiBgAffine_cycles,
    hleSwiObjAffine_cycles, hleSwiDecomp_cycles] | split | rfl)

theorem hleSwi_cycles (s : AGBState) (imm : Nat) :
    ((hleSwi s imm).1).cycles = s.cycles := by
  unfold hleSwi
  repeat (first | simp [biosSoftReset_cycles, biosRegReset_cycles,
    biosDiv_cycles, hleSwiHalt_cycles, hleSwiVBlankWait_cycles,
    hleSwiSqrt_cycles, hleSwiIntrWait_cycles, hleSwiCopy_cycles] | split | rfl)

theorem serviceSwi_cycles (s : AGBState) (a : UInt32) :
    (serviceSwi s a).cycles = s.cycles := by
  rfl

theorem busVal_cycles (s : AGBState) (v : UInt32) :
    ({ s with busVal := v }).cycles = s.cycles := by
  rfl

-- ── Block-transfer helpers preserve cycles ──

theorem pushRegs_cycles (s : AGBState) (b : UInt32) (xs : List Nat) :
    (pushRegs s b xs).cycles = s.cycles := by
  induction xs generalizing s b with
  | nil => rfl
  | cons r rs ih =>
    simp only [pushRegs]
    rw [ih]
    exact memWrite32_cycles _ _ _

theorem popRegs_cycles (s : AGBState) (b : UInt32) (xs : List Nat) :
    (popRegs s b xs).cycles = s.cycles := by
  induction xs generalizing s b with
  | nil => rfl
  | cons r rs ih =>
    simp only [popRegs]
    rw [ih]

-- ── Exact per-instruction costs ──

theorem exec_cost_movsImm (s : AGBState) (rd imm : Nat) :
    (execThumb s (.movsImm rd imm)).2 = 1 := by
  simp [execThumb]

theorem exec_cost_cmpImm (s : AGBState) (rn imm : Nat) :
    (execThumb s (.cmpImm rn imm)).2 = 1 := by
  simp [execThumb]

theorem exec_cost_addImm (s : AGBState) (rd imm : Nat) :
    (execThumb s (.addImm rd imm)).2 = 1 := by
  simp [execThumb]

theorem exec_cost_subImm (s : AGBState) (rd imm : Nat) :
    (execThumb s (.subImm rd imm)).2 = 1 := by
  simp [execThumb]

theorem exec_cost_addsImm (s : AGBState) (rd rn imm : Nat) :
    (execThumb s (.addsImm rd rn imm)).2 = 1 := by
  simp [execThumb]

theorem exec_cost_subsImm (s : AGBState) (rd rn imm : Nat) :
    (execThumb s (.subsImm rd rn imm)).2 = 1 := by
  simp [execThumb]

theorem exec_cost_addsReg (s : AGBState) (rd rn rm : Nat) :
    (execThumb s (.addsReg rd rn rm)).2 = 1 := by
  simp [execThumb]

theorem exec_cost_subsReg (s : AGBState) (rd rn rm : Nat) :
    (execThumb s (.subsReg rd rn rm)).2 = 1 := by
  simp [execThumb]

theorem exec_cost_lslImm (s : AGBState) (rd rm sh : Nat) :
    (execThumb s (.lslImm rd rm sh)).2 = 1 := by
  simp [execThumb]

theorem exec_cost_lsrImm (s : AGBState) (rd rm sh : Nat) :
    (execThumb s (.lsrImm rd rm sh)).2 = 1 := by
  simp [execThumb]

theorem exec_cost_asrImm (s : AGBState) (rd rm sh : Nat) :
    (execThumb s (.asrImm rd rm sh)).2 = 1 := by
  simp [execThumb]

theorem exec_cost_alu2 (s : AGBState) (op rs rd : Nat) :
    (execThumb s (.alu2 op rs rd)).2 = 1 := by
  simp [execThumb]

theorem exec_cost_mul (s : AGBState) (rs rd : Nat) :
    (execThumb s (.mul rs rd)).2 = 2 := by
  simp [execThumb]

theorem exec_cost_hiAdd (s : AGBState) (rs rd : Nat) :
    (execThumb s (.hiAdd rs rd)).2 = 1 := by
  simp [execThumb]

theorem exec_cost_hiCmp (s : AGBState) (rs rd : Nat) :
    (execThumb s (.hiCmp rs rd)).2 = 1 := by
  simp [execThumb]

theorem exec_cost_hiMov (s : AGBState) (rs rd : Nat) :
    (execThumb s (.hiMov rs rd)).2 = 1 := by
  simp [execThumb]

theorem exec_cost_strReg (s : AGBState) (rd rn rm : Nat) :
    (execThumb s (.strReg rd rn rm)).2 = 2 := by
  simp [execThumb]

theorem exec_cost_ldrReg (s : AGBState) (rd rn rm : Nat) :
    (execThumb s (.ldrReg rd rn rm)).2 = 3 := by
  simp [execThumb]

theorem exec_cost_strbReg (s : AGBState) (rd rn rm : Nat) :
    (execThumb s (.strbReg rd rn rm)).2 = 2 := by
  simp [execThumb]

theorem exec_cost_ldrbReg (s : AGBState) (rd rn rm : Nat) :
    (execThumb s (.ldrbReg rd rn rm)).2 = 3 := by
  simp [execThumb]

theorem exec_cost_strhReg (s : AGBState) (rd rn rm : Nat) :
    (execThumb s (.strhReg rd rn rm)).2 = 2 := by
  simp [execThumb]

theorem exec_cost_ldrhReg (s : AGBState) (rd rn rm : Nat) :
    (execThumb s (.ldrhReg rd rn rm)).2 = 3 := by
  simp [execThumb]

theorem exec_cost_ldsbReg (s : AGBState) (rd rn rm : Nat) :
    (execThumb s (.ldsbReg rd rn rm)).2 = 3 := by
  simp [execThumb]

theorem exec_cost_ldshReg (s : AGBState) (rd rn rm : Nat) :
    (execThumb s (.ldshReg rd rn rm)).2 = 3 := by
  simp [execThumb]

theorem exec_cost_strImm (s : AGBState) (rd rn off : Nat) :
    (execThumb s (.strImm rd rn off)).2 = 2 := by
  simp [execThumb]

theorem exec_cost_ldrImm (s : AGBState) (rd rn off : Nat) :
    (execThumb s (.ldrImm rd rn off)).2 = 3 := by
  simp [execThumb]

theorem exec_cost_strbImm (s : AGBState) (rd rn off : Nat) :
    (execThumb s (.strbImm rd rn off)).2 = 2 := by
  simp [execThumb]

theorem exec_cost_ldrbImm (s : AGBState) (rd rn off : Nat) :
    (execThumb s (.ldrbImm rd rn off)).2 = 3 := by
  simp [execThumb]

theorem exec_cost_strhImm (s : AGBState) (rd rn off : Nat) :
    (execThumb s (.strhImm rd rn off)).2 = 2 := by
  simp [execThumb]

theorem exec_cost_ldrhImm (s : AGBState) (rd rn off : Nat) :
    (execThumb s (.ldrhImm rd rn off)).2 = 3 := by
  simp [execThumb]

theorem exec_cost_strSp (s : AGBState) (rd off : Nat) :
    (execThumb s (.strSp rd off)).2 = 2 := by
  simp [execThumb]

theorem exec_cost_ldrSp (s : AGBState) (rd off : Nat) :
    (execThumb s (.ldrSp rd off)).2 = 3 := by
  simp [execThumb]

theorem exec_cost_ldrLit (s : AGBState) (rd off : Nat) :
    (execThumb s (.ldrLit rd off)).2 = 3 := by
  simp [execThumb]

theorem exec_cost_adrPc (s : AGBState) (rd off : Nat) :
    (execThumb s (.adrPc rd off)).2 = 1 := by
  simp [execThumb]

theorem exec_cost_adrSp (s : AGBState) (rd off : Nat) :
    (execThumb s (.adrSp rd off)).2 = 1 := by
  simp [execThumb]

theorem exec_cost_addSp (s : AGBState) (off : Int) :
    (execThumb s (.addSp off)).2 = 1 := by
  simp [execThumb]

theorem exec_cost_push (s : AGBState) (lr : Bool) (mask : Nat) :
    (execThumb s (.push lr mask)).2 = popcount mask + (if lr then 1 else 0) + 2 := by
  simp [execThumb]

theorem exec_cost_pop (s : AGBState) (pcBit : Bool) (mask : Nat) :
    (execThumb s (.pop pcBit mask)).2 = popcount mask + (if pcBit then 1 else 0) + 3 := by
  simp [execThumb]
  split <;> rfl

theorem exec_cost_stm (s : AGBState) (rb mask : Nat) :
    (execThumb s (.stm rb mask)).2 =
      if regList mask == [] then 4 else popcount mask + 2 := by
  simp [execThumb]
  split <;> rfl

theorem exec_cost_ldm (s : AGBState) (rb mask : Nat) :
    (execThumb s (.ldm rb mask)).2 =
      if regList mask == [] then 4 else popcount mask + 3 := by
  simp [execThumb]
  repeat (first | split | rfl)

theorem exec_cost_bcond (s : AGBState) (cond : Nat) (off : Int) :
    (execThumb s (.bcond cond off)).2 =
      if condPass s.regs.cpsr cond then 3 else 1 := by
  simp [execThumb]
  split <;> rfl

theorem exec_cost_b (s : AGBState) (off : Int) :
    (execThumb s (.b off)).2 = 3 := by
  simp [execThumb]

/-- Fast `B` equals the slow Thumb expression on its class
    (same fetch word, same `sx11` target, same cost, same tail). -/
theorem stepThumbFast_b_slow (s : AGBState) (pc w : UInt32)
    (hpc : pc = s.regs.pc)
    (h11 : (fetchHw w pc).toNat >>> 11 = 28) :
    stepThumbFast s pc w (fetchHw w pc)
      = some (let sL := { s with busVal := w };
              let ins := decodeThumb (fetchHw w pc);
              let (s2, c) := execThumb sL ins;
              advance s2 (c + memCost s pc 16 + execMemCostT s ins)) := by
  subst hpc
  unfold stepThumbFast stepThumbFastCore
  have hcond : (((fetchHw w s.regs.pc).toNat >>> 11 == 28) = true) :=
    beq_true_of_eq h11
  simp only [hcond, ite_true]
  rw [decodeThumb_b_eq _ h11]
  simp only [execThumb, execMemCostT]
  unfold advance
  simp only []
  congr 1

/-- Fast `MOVS` equals the slow Thumb expression on its class. -/
theorem stepThumbFast_movs_slow (s : AGBState) (pc w : UInt32) (hw : UInt16)
    (hpc : pc = s.regs.pc)
    (hB : ((hw.toNat >>> 11 == 28) = false))
    (h4 : hw.toNat >>> 11 = 4) :
    stepThumbFast s pc w hw
      = some (let sL := { s with busVal := w };
              let ins := decodeThumb hw;
              let (s2, c) := execThumb sL ins;
              advance s2 (c + memCost s pc 16 + execMemCostT s ins)) := by
  subst hpc
  unfold stepThumbFast stepThumbFastCore
  simp only [hB, ite_false, beq_true_of_eq h4, ite_true]
  rw [decodeThumb_movs_eq hw h4]
  simp only [execThumb, execMemCostT, applyNZCV, applyNZCVRegs, ArmRegs.set_cpsr]
  unfold advance
  simp only []
  congr 1

/-- Fast `CMP` equals the slow Thumb expression on its class. -/
theorem stepThumbFast_cmp_slow (s : AGBState) (pc w : UInt32) (hw : UInt16)
    (hpc : pc = s.regs.pc)
    (hB : ((hw.toNat >>> 11 == 28) = false))
    (h4f : ((hw.toNat >>> 11 == 4) = false))
    (h5 : hw.toNat >>> 11 = 5) :
    stepThumbFast s pc w hw
      = some (let sL := { s with busVal := w };
              let ins := decodeThumb hw;
              let (s2, c) := execThumb sL ins;
              advance s2 (c + memCost s pc 16 + execMemCostT s ins)) := by
  subst hpc
  unfold stepThumbFast stepThumbFastCore
  simp only [hB, ite_false, h4f, beq_true_of_eq h5, ite_true]
  rw [decodeThumb_cmp_eq hw h5]
  simp only [execThumb, execMemCostT, applyNZCV, applyNZCVRegs, ArmRegs.set_cpsr]
  unfold advance
  simp only []
  congr 1

/-- Fast `ADDS` (immediate) equals the slow Thumb expression. -/
theorem stepThumbFast_addsImm_slow (s : AGBState) (pc w : UInt32) (hw : UInt16)
    (hpc : pc = s.regs.pc)
    (hB : ((hw.toNat >>> 11 == 28) = false))
    (h4 : ((hw.toNat >>> 11 == 4) = false))
    (h5 : ((hw.toNat >>> 11 == 5) = false))
    (h11 : hw.toNat >>> 11 = 3)
    (hm : (hw.toNat >>> 10) % 2 = 1) (hl : (hw.toNat >>> 9) % 2 = 0) :
    stepThumbFast s pc w hw
      = some (let sL := { s with busVal := w };
              let ins := decodeThumb hw;
              let (s2, c) := execThumb sL ins;
              advance s2 (c + memCost s pc 16 + execMemCostT s ins)) := by
  subst hpc
  unfold stepThumbFast stepThumbFastCore
  have t3 : (((hw.toNat >>> 11 == 3) = true)) := beq_true_of_eq h11
  have tm : ((((hw.toNat >>> 10) % 2 == 1) = true)) := beq_true_of_eq hm
  have tl : ((((hw.toNat >>> 9) % 2 == 0) = true)) := beq_true_of_eq hl
  simp only [hB, h4, h5, t3, tm, tl, ite_false, ite_true,
    Bool.true_and, Bool.and_true]
  rw [decodeThumb_addsImm_eq hw h11 hm hl]
  simp only [execThumb, execMemCostT, applyNZCV, applyNZCVRegs, ArmRegs.set_cpsr]
  unfold advance
  simp only []
  congr 1

/-- Fast `SUBS` (immediate) equals the slow Thumb expression. -/
theorem stepThumbFast_subsImm_slow (s : AGBState) (pc w : UInt32) (hw : UInt16)
    (hpc : pc = s.regs.pc)
    (hB : ((hw.toNat >>> 11 == 28) = false))
    (h4 : ((hw.toNat >>> 11 == 4) = false))
    (h5 : ((hw.toNat >>> 11 == 5) = false))
    (h11 : hw.toNat >>> 11 = 3)
    (hm : (hw.toNat >>> 10) % 2 = 1) (hl : (hw.toNat >>> 9) % 2 = 1) :
    stepThumbFast s pc w hw
      = some (let sL := { s with busVal := w };
              let ins := decodeThumb hw;
              let (s2, c) := execThumb sL ins;
              advance s2 (c + memCost s pc 16 + execMemCostT s ins)) := by
  subst hpc
  unfold stepThumbFast stepThumbFastCore
  have t3 : (((hw.toNat >>> 11 == 3) = true)) := beq_true_of_eq h11
  have tm : ((((hw.toNat >>> 10) % 2 == 1) = true)) := beq_true_of_eq hm
  have tl : ((((hw.toNat >>> 9) % 2 == 1) = true)) := beq_true_of_eq hl
  have l0f : ((((hw.toNat >>> 9) % 2 == 0) = false)) :=
    beq_false_of_ne (by omega)
  simp only [hB, h4, h5, l0f, t3, tm, tl, ite_false, ite_true,
    Bool.true_and, Bool.and_true, Bool.and_false, Bool.false_and]
  rw [decodeThumb_subsImm_eq hw h11 hm hl]
  simp only [execThumb, execMemCostT, applyNZCV, applyNZCVRegs, ArmRegs.set_cpsr]
  unfold advance
  simp only []
  congr 1

/-- Fast `LSL` (immediate) equals the slow Thumb expression. -/
theorem stepThumbFast_lsl_slow (s : AGBState) (pc w : UInt32) (hw : UInt16)
    (hpc : pc = s.regs.pc)
    (hB : ((hw.toNat >>> 11 == 28) = false))
    (h4 : ((hw.toNat >>> 11 == 4) = false))
    (h5 : ((hw.toNat >>> 11 == 5) = false))
    (h3 : ((hw.toNat >>> 11 == 3) = false))
    (h0 : hw.toNat >>> 11 = 0) :
    stepThumbFast s pc w hw
      = some (let sL := { s with busVal := w };
              let ins := decodeThumb hw;
              let (s2, c) := execThumb sL ins;
              advance s2 (c + memCost s pc 16 + execMemCostT s ins)) := by
  subst hpc
  unfold stepThumbFast stepThumbFastCore
  have addsf : ((((hw.toNat >>> 11 == 3 && (hw.toNat >>> 10) % 2 == 1)
      && (hw.toNat >>> 9) % 2 == 0)) = false) := by simp [h3]
  have subsf : ((((hw.toNat >>> 11 == 3 && (hw.toNat >>> 10) % 2 == 1)
      && (hw.toNat >>> 9) % 2 == 1)) = false) := by simp [h3]
  simp only [hB, h4, h5, addsf, subsf, beq_true_of_eq h0, ite_false, ite_true]
  rw [decodeThumb_lsl_eq hw h0]
  simp only [execThumb, execMemCostT, applyNZCV, applyNZCVRegs, ArmRegs.set_cpsr]
  unfold advance
  simp only []
  congr 1

/-- Fast `ADDS` (register) equals the slow Thumb expression. -/
theorem stepThumbFast_addsReg_slow (s : AGBState) (pc w : UInt32) (hw : UInt16)
    (hpc : pc = s.regs.pc)
    (hB : ((hw.toNat >>> 11 == 28) = false))
    (h4 : ((hw.toNat >>> 11 == 4) = false))
    (h5 : ((hw.toNat >>> 11 == 5) = false))
    (h11 : hw.toNat >>> 11 = 3)
    (hm : (hw.toNat >>> 10) % 2 = 0) (hl : (hw.toNat >>> 9) % 2 = 0) :
    stepThumbFast s pc w hw
      = some (let sL := { s with busVal := w };
              let ins := decodeThumb hw;
              let (s2, c) := execThumb sL ins;
              advance s2 (c + memCost s pc 16 + execMemCostT s ins)) := by
  subst hpc
  unfold stepThumbFast stepThumbFastCore
  have t3 : (((hw.toNat >>> 11 == 3) = true)) := beq_true_of_eq h11
  have m0 : ((((hw.toNat >>> 10) % 2 == 0) = true)) := beq_true_of_eq hm
  have l0 : ((((hw.toNat >>> 9) % 2 == 0) = true)) := beq_true_of_eq hl
  have m1f : ((((hw.toNat >>> 10) % 2 == 1) = false)) :=
    beq_false_of_ne (by omega)
  have lslf : (((hw.toNat >>> 11 == 0) = false)) :=
    beq_false_of_ne (by omega)
  have lsrf : (((hw.toNat >>> 11 == 1) = false)) :=
    beq_false_of_ne (by omega)
  simp only [hB, h4, h5, m1f, lslf, lsrf, t3, m0, l0, ite_false, ite_true,
    Bool.true_and, Bool.and_true, Bool.and_false, Bool.false_and]
  rw [decodeThumb_addsReg_eq hw h11 hm hl]
  simp only [execThumb, execMemCostT, applyNZCV, applyNZCVRegs, ArmRegs.set_cpsr]
  unfold advance
  simp only []
  congr 1

/-- Fast `SUBS` (register) equals the slow Thumb expression. -/
theorem stepThumbFast_subsReg_slow (s : AGBState) (pc w : UInt32) (hw : UInt16)
    (hpc : pc = s.regs.pc)
    (hB : ((hw.toNat >>> 11 == 28) = false))
    (h4 : ((hw.toNat >>> 11 == 4) = false))
    (h5 : ((hw.toNat >>> 11 == 5) = false))
    (h11 : hw.toNat >>> 11 = 3)
    (hm : (hw.toNat >>> 10) % 2 = 0) (hl : (hw.toNat >>> 9) % 2 = 1) :
    stepThumbFast s pc w hw
      = some (let sL := { s with busVal := w };
              let ins := decodeThumb hw;
              let (s2, c) := execThumb sL ins;
              advance s2 (c + memCost s pc 16 + execMemCostT s ins)) := by
  subst hpc
  unfold stepThumbFast stepThumbFastCore
  have t3 : (((hw.toNat >>> 11 == 3) = true)) := beq_true_of_eq h11
  have m0 : ((((hw.toNat >>> 10) % 2 == 0) = true)) := beq_true_of_eq hm
  have l1 : ((((hw.toNat >>> 9) % 2 == 1) = true)) := beq_true_of_eq hl
  have m1f : ((((hw.toNat >>> 10) % 2 == 1) = false)) :=
    beq_false_of_ne (by omega)
  have l0f : ((((hw.toNat >>> 9) % 2 == 0) = false)) :=
    beq_false_of_ne (by omega)
  have lslf : (((hw.toNat >>> 11 == 0) = false)) :=
    beq_false_of_ne (by omega)
  have lsrf : (((hw.toNat >>> 11 == 1) = false)) :=
    beq_false_of_ne (by omega)
  simp only [hB, h4, h5, m1f, l0f, lslf, lsrf, t3, m0, l1,
    ite_false, ite_true, Bool.true_and, Bool.and_true, Bool.and_false,
    Bool.false_and]
  rw [decodeThumb_subsReg_eq hw h11 hm hl]
  simp only [execThumb, execMemCostT, applyNZCV, applyNZCVRegs, ArmRegs.set_cpsr]
  unfold advance
  simp only []
  congr 1

/-- Fast ALU two-operand class equals the slow Thumb expression. -/
theorem stepThumbFast_alu2_slow (s : AGBState) (pc w : UInt32) (hw : UInt16)
    (hpc : pc = s.regs.pc)
    (h10 : hw.toNat >>> 10 = 16)
    (hop : ((hw.toNat >>> 6) &&& 0xF == 13) = false) :
    stepThumbFast s pc w hw
      = some (let sL := { s with busVal := w };
              let ins := decodeThumb hw;
              let (s2, c) := execThumb sL ins;
              advance s2 (c + memCost s pc 16 + execMemCostT s ins)) := by
  subst hpc
  unfold stepThumbFast stepThumbFastCore
  have hBf : (((hw.toNat >>> 11 == 28) = false)) :=
    beq_false_of_ne (by omega)
  have h4f : (((hw.toNat >>> 11 == 4) = false)) :=
    beq_false_of_ne (by omega)
  have h5f : (((hw.toNat >>> 11 == 5) = false)) :=
    beq_false_of_ne (by omega)
  have t3f : (((hw.toNat >>> 11 == 3) = false)) :=
    beq_false_of_ne (by omega)
  have lslf : (((hw.toNat >>> 11 == 0) = false)) :=
    beq_false_of_ne (by omega)
  have lsrf : (((hw.toNat >>> 11 == 1) = false)) :=
    beq_false_of_ne (by omega)
  have t10 : (((hw.toNat >>> 10 == 16) = true)) := beq_true_of_eq h10
  simp only [hBf, h4f, h5f, t3f, lslf, lsrf, t10, hop, ite_false, ite_true,
    Bool.true_and, Bool.and_true, Bool.and_false, Bool.false_and]
  rw [decodeThumb_alu2_eq hw h10 hop]
  simp only [execThumb, execMemCostT, applyNZCV, applyNZCVRegs, ArmRegs.set_cpsr]
  unfold advance
  simp only []
  congr 1

/-- Fast `ADD` (small immediate) equals the slow Thumb expression. -/
theorem stepThumbFast_addImm_slow (s : AGBState) (pc w : UInt32) (hw : UInt16)
    (hpc : pc = s.regs.pc)
    (hB : ((hw.toNat >>> 11 == 28) = false))
    (h4 : ((hw.toNat >>> 11 == 4) = false))
    (h5 : ((hw.toNat >>> 11 == 5) = false))
    (h6 : hw.toNat >>> 11 = 6) :
    stepThumbFast s pc w hw
      = some (let sL := { s with busVal := w };
              let ins := decodeThumb hw;
              let (s2, c) := execThumb sL ins;
              advance s2 (c + memCost s pc 16 + execMemCostT s ins)) := by
  subst hpc
  unfold stepThumbFast stepThumbFastCore
  have t3f : (((hw.toNat >>> 11 == 3) = false)) :=
    beq_false_of_ne (by omega)
  have alu2f : (((hw.toNat >>> 10 == 16) = false)) :=
    beq_false_of_ne (by omega)
  have lslf : (((hw.toNat >>> 11 == 0) = false)) :=
    beq_false_of_ne (by omega)
  have lsrf : (((hw.toNat >>> 11 == 1) = false)) :=
    beq_false_of_ne (by omega)
  simp only [hB, h4, h5, t3f, alu2f, lslf, lsrf, beq_true_of_eq h6,
    ite_false, ite_true, Bool.true_and, Bool.and_true, Bool.and_false,
    Bool.false_and]
  rw [decodeThumb_addImm_eq hw h6]
  simp only [execThumb, execMemCostT, applyNZCV, applyNZCVRegs, ArmRegs.set_cpsr]
  unfold advance
  simp only []
  congr 1

/-- Fast `SUB` (small immediate) equals the slow Thumb expression. -/
theorem stepThumbFast_subImm_slow (s : AGBState) (pc w : UInt32) (hw : UInt16)
    (hpc : pc = s.regs.pc)
    (hB : ((hw.toNat >>> 11 == 28) = false))
    (h4 : ((hw.toNat >>> 11 == 4) = false))
    (h5 : ((hw.toNat >>> 11 == 5) = false))
    (h6 : ((hw.toNat >>> 11 == 6) = false))
    (h7 : hw.toNat >>> 11 = 7) :
    stepThumbFast s pc w hw
      = some (let sL := { s with busVal := w };
              let ins := decodeThumb hw;
              let (s2, c) := execThumb sL ins;
              advance s2 (c + memCost s pc 16 + execMemCostT s ins)) := by
  subst hpc
  unfold stepThumbFast stepThumbFastCore
  have t3f : (((hw.toNat >>> 11 == 3) = false)) :=
    beq_false_of_ne (by omega)
  have alu2f : (((hw.toNat >>> 10 == 16) = false)) :=
    beq_false_of_ne (by omega)
  have lslf : (((hw.toNat >>> 11 == 0) = false)) :=
    beq_false_of_ne (by omega)
  have lsrf : (((hw.toNat >>> 11 == 1) = false)) :=
    beq_false_of_ne (by omega)
  simp only [hB, h4, h5, h6, t3f, alu2f, lslf, lsrf, beq_true_of_eq h7,
    ite_false, ite_true, Bool.true_and, Bool.and_true, Bool.and_false,
    Bool.false_and]
  rw [decodeThumb_subImm_eq hw h7]
  simp only [execThumb, execMemCostT, applyNZCV, applyNZCVRegs, ArmRegs.set_cpsr]
  unfold advance
  simp only []
  congr 1

/-- Fast `ASR` (immediate) equals the slow Thumb expression. -/
theorem stepThumbFast_asr_slow (s : AGBState) (pc w : UInt32) (hw : UInt16)
    (hpc : pc = s.regs.pc)
    (hB : ((hw.toNat >>> 11 == 28) = false))
    (h4 : ((hw.toNat >>> 11 == 4) = false))
    (h5 : ((hw.toNat >>> 11 == 5) = false))
    (h6 : ((hw.toNat >>> 11 == 6) = false))
    (h7 : ((hw.toNat >>> 11 == 7) = false))
    (h2 : hw.toNat >>> 11 = 2) :
    stepThumbFast s pc w hw
      = some (let sL := { s with busVal := w };
              let ins := decodeThumb hw;
              let (s2, c) := execThumb sL ins;
              advance s2 (c + memCost s pc 16 + execMemCostT s ins)) := by
  subst hpc
  unfold stepThumbFast stepThumbFastCore
  have t3f : (((hw.toNat >>> 11 == 3) = false)) :=
    beq_false_of_ne (by omega)
  have alu2f : (((hw.toNat >>> 10 == 16) = false)) :=
    beq_false_of_ne (by omega)
  have lslf : (((hw.toNat >>> 11 == 0) = false)) :=
    beq_false_of_ne (by omega)
  have lsrf : (((hw.toNat >>> 11 == 1) = false)) :=
    beq_false_of_ne (by omega)
  simp only [hB, h4, h5, h6, h7, t3f, alu2f, lslf, lsrf, beq_true_of_eq h2,
    ite_false, ite_true, Bool.true_and, Bool.and_true, Bool.and_false,
    Bool.false_and]
  rw [decodeThumb_asr_eq hw h2]
  simp only [execThumb, execMemCostT, applyNZCV, applyNZCVRegs, ArmRegs.set_cpsr]
  unfold advance
  simp only []
  congr 1

/-- Fast conditional branch equals the slow Thumb expression. -/
theorem stepThumbFast_bcond_slow (s : AGBState) (pc w : UInt32) (hw : UInt16)
    (hpc : pc = s.regs.pc)
    (h12 : hw.toNat >>> 12 = 13)
    (hne : ((hw.toNat >>> 8) &&& 0xF == 14) = false)
    (hswi : ((hw.toNat >>> 8 == 223) = false)) :
    stepThumbFast s pc w hw
      = some (let sL := { s with busVal := w };
              let ins := decodeThumb hw;
              let (s2, c) := execThumb sL ins;
              advance s2 (c + memCost s pc 16 + execMemCostT s ins)) := by
  subst hpc
  unfold stepThumbFast stepThumbFastCore
  have hBf : (((hw.toNat >>> 11 == 28) = false)) :=
    beq_false_of_ne (by omega)
  have h4f : (((hw.toNat >>> 11 == 4) = false)) :=
    beq_false_of_ne (by omega)
  have h5f : (((hw.toNat >>> 11 == 5) = false)) :=
    beq_false_of_ne (by omega)
  have h6f : (((hw.toNat >>> 11 == 6) = false)) :=
    beq_false_of_ne (by omega)
  have h7f : (((hw.toNat >>> 11 == 7) = false)) :=
    beq_false_of_ne (by omega)
  have h0f : (((hw.toNat >>> 11 == 0) = false)) :=
    beq_false_of_ne (by omega)
  have h1f : (((hw.toNat >>> 11 == 1) = false)) :=
    beq_false_of_ne (by omega)
  have h2f : (((hw.toNat >>> 11 == 2) = false)) :=
    beq_false_of_ne (by omega)
  have h10f : (((hw.toNat >>> 10 == 16) = false)) :=
    beq_false_of_ne (by omega)
  have t12 : ((hw.toNat >>> 12 == 13) = true) := beq_true_of_eq h12
  have t3f : (((hw.toNat >>> 11 == 3) = false)) :=
    beq_false_of_ne (by omega)
  have tbc : ((((hw.toNat >>> 12 == 13) && (((hw.toNat >>> 8) &&& 0xF == 14) == false))
      && (((hw.toNat >>> 8) == 223) == false)) = true) := by
    simp [t12, hne, hswi]
  simp only [tbc, t3f, hBf, h4f, h5f, h6f, h7f, h0f, h1f, h2f,
    h10f, ite_false, ite_true, Bool.false_eq_true, Bool.true_and,
    Bool.and_true, Bool.and_false, Bool.false_and]
  rw [decodeThumb_bcond_eq hw h12 hne hswi]
  simp only [execThumb, execMemCostT]
  by_cases hcp : condPass s.regs.cpsr ((hw.toNat >>> 8) &&& 0xF)
  · simp only [hcp, ite_true]
    unfold advance
    simp only []
    congr 1
  · simp only [hcp, Bool.false_eq_true, ite_false]
    unfold advance
    simp only []
    congr 1

/-- Fast `LSR` (immediate) equals the slow Thumb expression. -/
theorem stepThumbFast_lsr_slow (s : AGBState) (pc w : UInt32) (hw : UInt16)
    (hpc : pc = s.regs.pc)
    (hB : ((hw.toNat >>> 11 == 28) = false))
    (h4 : ((hw.toNat >>> 11 == 4) = false))
    (h5 : ((hw.toNat >>> 11 == 5) = false))
    (h3 : ((hw.toNat >>> 11 == 3) = false))
    (h0 : ((hw.toNat >>> 11 == 0) = false))
    (h1 : hw.toNat >>> 11 = 1) :
    stepThumbFast s pc w hw
      = some (let sL := { s with busVal := w };
              let ins := decodeThumb hw;
              let (s2, c) := execThumb sL ins;
              advance s2 (c + memCost s pc 16 + execMemCostT s ins)) := by
  subst hpc
  unfold stepThumbFast stepThumbFastCore
  have addsf : ((((hw.toNat >>> 11 == 3 && (hw.toNat >>> 10) % 2 == 1)
      && (hw.toNat >>> 9) % 2 == 0)) = false) := by simp [h3]
  have subsf : ((((hw.toNat >>> 11 == 3 && (hw.toNat >>> 10) % 2 == 1)
      && (hw.toNat >>> 9) % 2 == 1)) = false) := by simp [h3]
  simp only [hB, h4, h5, addsf, subsf, h0, beq_true_of_eq h1, ite_false, ite_true]
  rw [decodeThumb_lsr_eq hw h1]
  simp only [execThumb, execMemCostT, applyNZCV, applyNZCVRegs, ArmRegs.set_cpsr]
  unfold advance
  simp only []
  congr 1

theorem exec_cost_blPre (s : AGBState) (off : Int) :
    (execThumb s (.blPre off)).2 = 3 := by
  simp [execThumb]

theorem exec_cost_blSuf (s : AGBState) (off : Int) :
    (execThumb s (.blSuf off)).2 = 4 := by
  simp [execThumb]

theorem exec_cost_bx (s : AGBState) (rm : Nat) :
    (execThumb s (.bx rm)).2 = 3 := by
  simp [execThumb]

theorem exec_cost_swi (s : AGBState) (imm : Nat) :
    (execThumb s (.swi imm)).2 = 2 := by
  simp [execThumb]
  split <;> rfl

theorem exec_cost_nop (s : AGBState) : (execThumb s .nop).2 = 1 := by
  simp [execThumb]

/-- Every instruction costs ≥ 1 cycle (lower bound for monotonicity). -/
theorem exec_cost_ge1 (s : AGBState) (ins : ThumbInstr) : 1 ≤ (execThumb s ins).2 := by
  cases ins <;> simp [execThumb] <;> repeat (first | split | omega)

-- ── Executor preserves wall-clock (advance owns time) ──

theorem applyNZCV_cycles (s : AGBState) (f : NZCV) :
    (applyNZCV s f).cycles = s.cycles := by
  rfl

theorem fixLoadedPC_cycles (s : AGBState) (v : UInt32) :
    (fixLoadedPC s v).cycles = s.cycles := by
  rfl

theorem execThumb_cycles (s : AGBState) (ins : ThumbInstr) :
    ((execThumb s ins).1).cycles = s.cycles := by
  cases ins <;>
    simp [execThumb, applyNZCV_cycles, fixLoadedPC_cycles, memWrite32_cycles,
      memWrite16_cycles, memWrite8_cycles, hleSwi_cycles,
      memRead8E_cycles, memRead16E_cycles, memRead32E_cycles,
      pushRegs_cycles, popRegs_cycles] <;>
    repeat (first | split |
      simp [fixLoadedPC_cycles, popRegs_cycles, serviceSwi_cycles, hleSwi_cycles,
        memRead8E_cycles, memRead16E_cycles, memRead32E_cycles] | rfl)






-- ── ARM executor helpers preserve cycles ──

theorem execDp_cost (s : AGBState) (op st rn rd : Nat) (y : UInt32) (shC : Bool) :
    (execDp s op st rn rd y shC).2 = 1 := by
  unfold execDp
  dsimp only
  repeat (first | split | rfl)

theorem execDp_cycles (s : AGBState) (op st rn rd : Nat) (y : UInt32) (shC : Bool) :
    ((execDp s op st rn rd y shC).1).cycles = s.cycles := by
  unfold execDp
  repeat (first | split | simp [applyNZCV_cycles] | rfl)

theorem memAddrWB_cycles (s : AGBState) (rn : Nat) (p u w : Bool) (off : UInt32) :
    ((memAddrWB s rn p u w off).1).cycles = s.cycles := by
  unfold memAddrWB
  repeat (first | split | rfl)

theorem applyMsr_cycles (s : AGBState) (psr mask : Nat) (v : UInt32) :
    (applyMsr s psr mask v).cycles = s.cycles := by
  unfold applyMsr
  repeat (first | split | rfl)

theorem writePC_cycles (s : AGBState) (v : UInt32) :
    (writePC s v).cycles = s.cycles := by
  rfl

-- ── Exact ARM per-instruction costs ──

theorem execArm_cost_dpImm (s : AGBState) (c op st rn rd rot imm8 : Nat) :
    (execArm s (.dpImm c op st rn rd rot imm8)).2 = 1 := by
  by_cases h : armCondPass s.regs.cpsr c <;> simp [execArm, execDp_cost, h] <;> repeat (first | split | rfl)

theorem execArm_cost_dpReg (s : AGBState) (c op st rn rd rm shTy : Nat) (shReg : Bool)
    (sa : Nat) :
    (execArm s (.dpReg c op st rn rd rm shTy shReg sa)).2 = 1 := by
  by_cases h : armCondPass s.regs.cpsr c <;> simp [execArm, execDp_cost, h] <;> repeat (first | split | rfl)

theorem execArm_cost_mul (s : AGBState) (c : Nat) (acc st : Bool) (rd rn rm rs : Nat) :
    (execArm s (.mul c acc st rd rn rm rs)).2 =
      if armCondPass s.regs.cpsr c then 2 else 1 := by
  by_cases h : armCondPass s.regs.cpsr c <;> simp [execArm, h] <;> repeat (first | split | rfl)

theorem execArm_cost_mull (s : AGBState) (c : Nat) (u acc st : Bool)
    (rdHi rdLo rm rs : Nat) :
    (execArm s (.mull c u acc st rdHi rdLo rm rs)).2 =
      if armCondPass s.regs.cpsr c then 3 else 1 := by
  by_cases h : armCondPass s.regs.cpsr c <;> simp [execArm, h] <;> repeat (first | split | rfl)

theorem execArm_cost_mrs (s : AGBState) (c psr rd : Nat) :
    (execArm s (.mrs c psr rd)).2 = 1 := by
  by_cases h : armCondPass s.regs.cpsr c <;> simp [execArm, h] <;> repeat (first | split | rfl)

theorem execArm_cost_msrImm (s : AGBState) (c psr mask rot imm8 : Nat) :
    (execArm s (.msrImm c psr mask rot imm8)).2 = 1 := by
  by_cases h : armCondPass s.regs.cpsr c <;> simp [execArm, h] <;> repeat (first | split | rfl)

theorem execArm_cost_msrReg (s : AGBState) (c psr mask rm : Nat) :
    (execArm s (.msrReg c psr mask rm)).2 = 1 := by
  by_cases h : armCondPass s.regs.cpsr c <;> simp [execArm, h] <;> repeat (first | split | rfl)

theorem execArm_cost_memImm (s : AGBState) (c : Nat) (p u b w l : Bool)
    (rn rd off12 : Nat) :
    (execArm s (.memImm c p u b w l rn rd off12)).2 =
      if armCondPass s.regs.cpsr c then (if l then 3 else 2) else 1 := by
  by_cases h : armCondPass s.regs.cpsr c <;> simp [execArm, h] <;> repeat (first | split | rfl)

theorem execArm_cost_memReg (s : AGBState) (c : Nat) (p u b w l : Bool)
    (rn rd rm shTy amt5 : Nat) :
    (execArm s (.memReg c p u b w l rn rd rm shTy amt5)).2 =
      if armCondPass s.regs.cpsr c then (if l then 3 else 2) else 1 := by
  by_cases h : armCondPass s.regs.cpsr c <;> simp [execArm, h] <;> repeat (first | split | rfl)

theorem execArm_cost_memH (s : AGBState) (c : Nat) (p u w l h hh : Bool)
    (rn rd : Nat) (isImm : Bool) (off : Nat) :
    (execArm s (.memH c p u w l h hh rn rd isImm off)).2 =
      if armCondPass s.regs.cpsr c then (if l then 3 else 2) else 1 := by
  by_cases h : armCondPass s.regs.cpsr c <;> simp [execArm, h] <;> repeat (first | split | rfl)

theorem execArm_cost_ldmStm (s : AGBState) (c : Nat) (p u st w l : Bool)
    (rn mask : Nat) :
    (execArm s (.ldmStm c p u st w l rn mask)).2 =
      if armCondPass s.regs.cpsr c then
        (if regList16 mask == [] then 4
         else popcount16 mask + (if l then 3 else 2))
      else 1 := by
  by_cases h : armCondPass s.regs.cpsr c <;> simp [execArm, h] <;> repeat (first | split | rfl)

theorem execArm_cost_b (s : AGBState) (c : Nat) (off : Int) :
    (execArm s (.b c off)).2 = if armCondPass s.regs.cpsr c then 3 else 1 := by
  by_cases h : armCondPass s.regs.cpsr c <;> simp [execArm, h] <;> repeat (first | split | rfl)

theorem execArm_cost_bl (s : AGBState) (c : Nat) (off : Int) :
    (execArm s (.bl c off)).2 = if armCondPass s.regs.cpsr c then 4 else 1 := by
  by_cases h : armCondPass s.regs.cpsr c <;> simp [execArm, h] <;> repeat (first | split | rfl)

theorem execArm_cost_bx (s : AGBState) (c rm : Nat) :
    (execArm s (.bx c rm)).2 = if armCondPass s.regs.cpsr c then 3 else 1 := by
  by_cases h : armCondPass s.regs.cpsr c <;> simp [execArm, h] <;> repeat (first | split | rfl)

theorem execArm_cost_swi (s : AGBState) (c imm : Nat) :
    (execArm s (.swi c imm)).2 = if armCondPass s.regs.cpsr c then 2 else 1 := by
  by_cases h : armCondPass s.regs.cpsr c <;> simp [execArm, h] <;> repeat (first | split | rfl)

theorem execArm_cost_swp (s : AGBState) (c : Nat) (b : Bool) (rn rd rm : Nat) :
    (execArm s (.swp c b rn rd rm)).2 =
      if armCondPass s.regs.cpsr c then 3 else 1 := by
  by_cases h : armCondPass s.regs.cpsr c <;> simp [execArm, h] <;> repeat (first | split | rfl)

theorem execArm_cost_nop (s : AGBState) : (execArm s .nop).2 = 1 := by
  simp [execArm]

-- ── Per-arm cycle preservation (by_cases-first: the RHS has no ifs,
-- so splits stay consistent, unlike the cost statements) ──

theorem execArm_cyc_dpImm (s : AGBState) (c op st rn rd rot imm8 : Nat) :
    ((execArm s (.dpImm c op st rn rd rot imm8)).1).cycles = s.cycles := by
  by_cases h : armCondPass s.regs.cpsr c <;> simp [execArm, h, execDp_cycles] <;> rfl

theorem execArm_cyc_dpReg (s : AGBState) (c op st rn rd rm shTy : Nat) (shReg : Bool)
    (sa : Nat) :
    ((execArm s (.dpReg c op st rn rd rm shTy shReg sa)).1).cycles = s.cycles := by
  by_cases h : armCondPass s.regs.cpsr c <;> simp [execArm, h, execDp_cycles] <;> rfl

theorem execArm_cyc_mul (s : AGBState) (c : Nat) (acc st : Bool) (rd rn rm rs : Nat) :
    ((execArm s (.mul c acc st rd rn rm rs)).1).cycles = s.cycles := by
  by_cases h : armCondPass s.regs.cpsr c <;> simp [execArm, h] <;>
    repeat (first | split | simp [applyNZCV_cycles] | rfl)

theorem execArm_cyc_mull (s : AGBState) (c : Nat) (u acc st : Bool)
    (rdHi rdLo rm rs : Nat) :
    ((execArm s (.mull c u acc st rdHi rdLo rm rs)).1).cycles = s.cycles := by
  by_cases h : armCondPass s.regs.cpsr c <;> simp [execArm, h] <;>
    repeat (first | split | simp [applyNZCV_cycles] | rfl)

theorem execArm_cyc_mrs (s : AGBState) (c psr rd : Nat) :
    ((execArm s (.mrs c psr rd)).1).cycles = s.cycles := by
  by_cases h : armCondPass s.regs.cpsr c <;> simp [execArm, h] <;> rfl

theorem execArm_cyc_msrImm (s : AGBState) (c psr mask rot imm8 : Nat) :
    ((execArm s (.msrImm c psr mask rot imm8)).1).cycles = s.cycles := by
  by_cases h : armCondPass s.regs.cpsr c <;> simp [execArm, h, applyMsr_cycles] <;> rfl

theorem execArm_cyc_msrReg (s : AGBState) (c psr mask rm : Nat) :
    ((execArm s (.msrReg c psr mask rm)).1).cycles = s.cycles := by
  by_cases h : armCondPass s.regs.cpsr c <;> simp [execArm, h, applyMsr_cycles] <;> rfl

theorem execArm_cyc_memImm (s : AGBState) (c : Nat) (p u b w l : Bool)
    (rn rd off12 : Nat) :
    ((execArm s (.memImm c p u b w l rn rd off12)).1).cycles = s.cycles := by
  by_cases h : armCondPass s.regs.cpsr c <;>
    simp [execArm, h, memAddrWB_cycles] <;>
    repeat (first | split | simp [memAddrWB_cycles, memWrite32_cycles,
      memWrite8_cycles, memRead8E_cycles, memRead32E_cycles, writePC_cycles] | rfl)

theorem execArm_cyc_memReg (s : AGBState) (c : Nat) (p u b w l : Bool)
    (rn rd rm shTy amt5 : Nat) :
    ((execArm s (.memReg c p u b w l rn rd rm shTy amt5)).1).cycles = s.cycles := by
  by_cases h : armCondPass s.regs.cpsr c <;>
    simp [execArm, h, memAddrWB_cycles] <;>
    repeat (first | split | simp [memAddrWB_cycles, memWrite32_cycles,
      memWrite8_cycles, memRead8E_cycles, memRead32E_cycles, writePC_cycles] | rfl)

theorem execArm_cyc_memH (s : AGBState) (c : Nat) (p u w l h hh : Bool)
    (rn rd : Nat) (isImm : Bool) (off : Nat) :
    ((execArm s (.memH c p u w l h hh rn rd isImm off)).1).cycles = s.cycles := by
  by_cases h : armCondPass s.regs.cpsr c <;>
    simp [execArm, h] <;>
    repeat (first | split | simp [memAddrWB_cycles, memWrite16_cycles,
      memRead8E_cycles, memRead16E_cycles, writePC_cycles] | rfl)

theorem execArm_cyc_ldmStm (s : AGBState) (c : Nat) (p u st w l : Bool)
    (rn mask : Nat) :
    ((execArm s (.ldmStm c p u st w l rn mask)).1).cycles = s.cycles := by
  by_cases h : armCondPass s.regs.cpsr c <;>
    simp [execArm, h, memWrite32_cycles, pushRegs_cycles, popRegs_cycles] <;>
    repeat (first | split |
      simp [pushRegs_cycles, popRegs_cycles, fixLoadedPC_cycles,
        writePC_cycles] | rfl)

theorem execArm_cyc_b (s : AGBState) (c : Nat) (off : Int) :
    ((execArm s (.b c off)).1).cycles = s.cycles := by
  by_cases h : armCondPass s.regs.cpsr c <;> simp [execArm, h] <;> rfl

theorem execArm_cyc_bl (s : AGBState) (c : Nat) (off : Int) :
    ((execArm s (.bl c off)).1).cycles = s.cycles := by
  by_cases h : armCondPass s.regs.cpsr c <;> simp [execArm, h] <;> rfl

theorem execArm_cyc_bx (s : AGBState) (c rm : Nat) :
    ((execArm s (.bx c rm)).1).cycles = s.cycles := by
  by_cases h : armCondPass s.regs.cpsr c <;> simp [execArm, h] <;> rfl

theorem execArm_cyc_swi (s : AGBState) (c imm : Nat) :
    ((execArm s (.swi c imm)).1).cycles = s.cycles := by
  by_cases h : armCondPass s.regs.cpsr c <;>
    simp [execArm, h, hleSwi_cycles] <;>
    repeat (first | split | simp [hleSwi_cycles, serviceSwi_cycles] | rfl)

theorem execArm_cyc_swp (s : AGBState) (c : Nat) (b : Bool) (rn rd rm : Nat) :
    ((execArm s (.swp c b rn rd rm)).1).cycles = s.cycles := by
  by_cases h : armCondPass s.regs.cpsr c <;>
    simp [execArm, h] <;>
    repeat (first | split | simp [memWrite32_cycles, memWrite8_cycles,
      memRead8E_cycles, memRead32E_cycles] | rfl)

theorem execArm_cyc_nop (s : AGBState) : ((execArm s .nop).1).cycles = s.cycles := by
  simp [execArm]

theorem execArm_cost_ge1 (s : AGBState) (ins : ArmInstr) : 1 ≤ (execArm s ins).2 := by
  cases ins <;>
    simp [execArm_cost_dpImm, execArm_cost_dpReg, execArm_cost_mul, execArm_cost_mull,
      execArm_cost_mrs, execArm_cost_msrImm, execArm_cost_msrReg, execArm_cost_memImm,
      execArm_cost_memReg, execArm_cost_memH, execArm_cost_ldmStm, execArm_cost_b,
      execArm_cost_bl, execArm_cost_bx, execArm_cost_swi, execArm_cost_swp,
      execArm_cost_nop] <;>
    repeat (first | split | omega)

theorem execArm_cycles (s : AGBState) (ins : ArmInstr) :
    ((execArm s ins).1).cycles = s.cycles := by
  cases ins <;>
    simp [execArm_cyc_dpImm, execArm_cyc_dpReg, execArm_cyc_mul, execArm_cyc_mull,
      execArm_cyc_mrs, execArm_cyc_msrImm, execArm_cyc_msrReg, execArm_cyc_memImm,
      execArm_cyc_memReg, execArm_cyc_memH, execArm_cyc_ldmStm, execArm_cyc_b,
      execArm_cyc_bl, execArm_cyc_bx, execArm_cyc_swi, execArm_cyc_swp, execArm_cyc_nop]

-- ── Every CPU step advances time ──

theorem stepCPU_mono (s : AGBState) : s.cycles ≤ (stepCPU s).cycles := by
  unfold stepCPU
  dsimp only
  split
  · split
    · split
      · rw [advance_cycles, serviceIrq_cycles]
        exact Nat.le_add_right s.cycles 3
      · rw [advance_cycles]
        exact Nat.le_add_right s.cycles 1
    · rw [advance_cycles]
      exact Nat.le_add_right s.cycles 1
  · split
    · rw [advance_cycles, serviceIrq_cycles]
      exact Nat.le_add_right s.cycles 3
    · split
      · split
        · next h => exact stepThumbFast_some_mono _ _ _ _ _ h
        · simp [advance_cycles, execThumb_cycles]
      · simp [advance_cycles, execArm_cycles]

-- ── Bounded reachability: concrete 4-instruction program ──

/-- `MOVS r0,#0x45 | MOVS r1,#0x38 | ADDS r2,r0,r1 | B .` -/
def execROM : ByteArray :=
  ByteArray.mk #[0x45, 0x20, 0x38, 0x21, 0x42, 0x18, 0xFE, 0xE7]

theorem exec_reaches_add :
    (runInstrs (loadROM execROM) 3).regs.get 2 = 0x7D := by
  decide

theorem exec_pc_after_movs :
    (runInstrs (loadROM execROM) 1).regs.pc = 0x08000002 := by
  decide

theorem exec_spins_in_loop :
    (runInstrs (loadROM execROM) 5).regs.pc = 0x08000006 := by
  decide

theorem exec_flags_after_movs :
    cpsrZ ((stepCPU (loadROM execROM)).regs.cpsr) = false := by
  decide

theorem exec_halt_freezes_pc :
    ((runInstrs ((hleSwi (loadROM execROM) SWI_HALT).1) 4).regs.pc) = 0x08000000 := by
  decide

end AGB
