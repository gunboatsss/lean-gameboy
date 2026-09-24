/-
  LeanAGB.Cpu.Regs — ARM7TDMI register file + CPSR.
  Full bank file (USR/SYS shared view in `r`, banked slots per mode).
  `get`/`set` resolve through the CURRENT CPSR mode, so instruction
  execution needs no manual swapping; exception entry only writes the
  new mode's SPSR/LR slots (the switch itself is the bank switch).
  GBA has no MMU/MPU, so ABT/UND entries never fire on HW — their
  slots exist for model completeness.
-/
import LeanAGB.Basic

namespace AGB

/-- CPSR flag bit positions (ARM ARM §A2): N=31 Z=30 C=29 V=28, T=5. -/
def CPSR_N : Nat := 31
def CPSR_Z : Nat := 30
def CPSR_C : Nat := 29
def CPSR_V : Nat := 28
/-- N flag (bit 31). -/
def cpsrN (cpsr : UInt32) : Bool := bitGet32 cpsr 31
/-- Z flag (bit 30). -/
def cpsrZ (cpsr : UInt32) : Bool := bitGet32 cpsr 30
/-- C flag (bit 29). -/
def cpsrC (cpsr : UInt32) : Bool := bitGet32 cpsr 29
/-- V flag (bit 28). -/
def cpsrV (cpsr : UInt32) : Bool := bitGet32 cpsr 28
/-- T state bit (bit 5): true = Thumb. -/
def cpsrT (cpsr : UInt32) : Bool := bitGet32 cpsr 5

/-- 14 ARM condition codes (ARM ARM DDI 0100I, Thumb Bcond / ARM cond field).
    14 (AL) and 15 (NV) never pass here: in Thumb, 0xDFxx is SWI and
    1110 is UNDEFINED, so the decoder never produces them. -/
def condPass (cpsr : UInt32) (cond : Nat) : Bool :=
  let n := cpsrN cpsr; let z := cpsrZ cpsr
  let c := cpsrC cpsr; let v := cpsrV cpsr
  match cond with
  | 0 => z           -- EQ
  | 1 => !z          -- NE
  | 2 => c           -- CS/HS
  | 3 => !c          -- CC/LO
  | 4 => n           -- MI
  | 5 => !n          -- PL
  | 6 => v           -- VS
  | 7 => !v          -- VC
  | 8 => c && !z     -- HI
  | 9 => !c || z     -- LS
  | 10 => n == v     -- GE
  | 11 => n != v     -- LT
  | 12 => !z && (n == v)  -- GT
  | 13 => z || (n != v)   -- LE
  | _ => false

/-- ARM condition check: AL (14) always passes; NV (15) never does
    (v4T has no v5 unconditional-extension space). Thumb Bcond keeps
    using `condPass` directly (its decoder never emits 14/15). -/
def armCondPass (cpsr : UInt32) (cond : Nat) : Bool :=
  if cond == 14 then true else condPass cpsr cond

/-- Current processor mode number (low 5 CPSR bits). -/
def cpsrMode (cpsr : UInt32) : Nat := cpsr.toNat &&& 0x1F

/-- Set N/Z/C/V in one go (data-processing with S). -/
def cpsrSetNZCV (cpsr : UInt32) (n z c v : Bool) : UInt32 :=
  let cf := fun (x : UInt32) (i : Nat) (b : Bool) =>
    if b then bitSet32 x i else bitClear32 x i
  cf (cf (cf (cf cpsr 31 n) 30 z) 29 c) 28 v

/-- Processor modes (low 5 bits of CPSR). -/
def MODE_USR : UInt8 := 0x10
def MODE_FIQ : UInt8 := 0x11
def MODE_IRQ : UInt8 := 0x12
def MODE_SVC : UInt8 := 0x13
def MODE_ABT : UInt8 := 0x17
def MODE_UND : UInt8 := 0x1B
def MODE_SYS : UInt8 := 0x1F

/-- 16 general regs: r0–r7 + r8–r12 USR/SYS view + r13/r14 USR/SYS
    view + PC. Banked views live in the slots below. -/
structure ArmRegs where
  r : Array UInt32 := Array.replicate 16 0
  cpsr : UInt32 := 0x1F  -- SYS mode, ARM state
  spsr_fiq : UInt32 := 0
  spsr_svc : UInt32 := 0
  spsr_irq : UInt32 := 0
  spsr_abt : UInt32 := 0
  spsr_und : UInt32 := 0
  fiqHi : Array UInt32 := Array.replicate 5 0  -- r8–r12 FIQ view
  r13_fiq : UInt32 := 0
  r14_fiq : UInt32 := 0
  r13_svc : UInt32 := 0
  r14_svc : UInt32 := 0
  r13_irq : UInt32 := 0
  r14_irq : UInt32 := 0
  r13_abt : UInt32 := 0
  r14_abt : UInt32 := 0
  r13_und : UInt32 := 0
  r14_und : UInt32 := 0
deriving DecidableEq, Repr

/-- Mode-aware read: FIQ sees its own r8–r14; each privileged mode
    sees its own r13/r14; USR/SYS share the `r` view; PC never banks. -/
@[inline] def ArmRegs.get (rs : ArmRegs) (i : Nat) : UInt32 :=
  let m := cpsrMode rs.cpsr
  if i == 15 then rs.r.getD 15 0
  else if i == 13 || i == 14 then
    if m == MODE_FIQ.toNat then (if i == 13 then rs.r13_fiq else rs.r14_fiq)
    else if m == MODE_IRQ.toNat then (if i == 13 then rs.r13_irq else rs.r14_irq)
    else if m == MODE_SVC.toNat then (if i == 13 then rs.r13_svc else rs.r14_svc)
    else if m == MODE_ABT.toNat then (if i == 13 then rs.r13_abt else rs.r14_abt)
    else if m == MODE_UND.toNat then (if i == 13 then rs.r13_und else rs.r14_und)
    else rs.r.getD i 0
  else if 8 <= i && i <= 12 then
    if m == MODE_FIQ.toNat then rs.fiqHi.getD (i - 8) 0 else rs.r.getD i 0
  else rs.r.getD i 0

/-- Mode-aware write (mirrors `get`). -/
@[inline] def ArmRegs.set (rs : ArmRegs) (i : Nat) (v : UInt32) : ArmRegs :=
  let m := cpsrMode rs.cpsr
  if i == 15 then { rs with r := rs.r.set! 15 v }
  else if i == 13 || i == 14 then
    if m == MODE_FIQ.toNat then
      (if i == 13 then { rs with r13_fiq := v } else { rs with r14_fiq := v })
    else if m == MODE_IRQ.toNat then
      (if i == 13 then { rs with r13_irq := v } else { rs with r14_irq := v })
    else if m == MODE_SVC.toNat then
      (if i == 13 then { rs with r13_svc := v } else { rs with r14_svc := v })
    else if m == MODE_ABT.toNat then
      (if i == 13 then { rs with r13_abt := v } else { rs with r14_abt := v })
    else if m == MODE_UND.toNat then
      (if i == 13 then { rs with r13_und := v } else { rs with r14_und := v })
    else { rs with r := rs.r.set! i v }
  else if 8 <= i && i <= 12 then
    if m == MODE_FIQ.toNat then { rs with fiqHi := rs.fiqHi.set! (i - 8) v }
    else { rs with r := rs.r.set! i v }
  else { rs with r := rs.r.set! i v }

def ArmRegs.pc (rs : ArmRegs) : UInt32 := rs.get 15

/-- Current mode's SPSR (for MRS / exception returns). USR/SYS have no
    SPSR on HW (UNPREDICTABLE); the model returns CPSR itself, making
    MOVS PC,LR there a plain branch. -/
def spsrOf (rs : ArmRegs) : UInt32 :=
  match cpsrMode rs.cpsr with
  | 0x11 => rs.spsr_fiq
  | 0x12 => rs.spsr_irq
  | 0x13 => rs.spsr_svc
  | 0x17 => rs.spsr_abt
  | 0x1B => rs.spsr_und
  | _ => rs.cpsr

/-- Write the current mode's SPSR (no-op in USR/SYS: none exists). -/
def setSpsr (rs : ArmRegs) (v : UInt32) : ArmRegs :=
  match cpsrMode rs.cpsr with
  | 0x11 => { rs with spsr_fiq := v }
  | 0x12 => { rs with spsr_irq := v }
  | 0x13 => { rs with spsr_svc := v }
  | 0x17 => { rs with spsr_abt := v }
  | 0x1B => { rs with spsr_und := v }
  | _ => rs

/-- CPSR surgery for exception entry: install mode, force ARM state,
    optionally mask IRQ/FIQ. I is masked on IRQ (not on SVC); F is
    masked only on FIQ (GBA BIOS never uses FIQ; no entry modeled). -/
def excCpsr (old : UInt32) (newMode : UInt8) (maskI maskF : Bool) : UInt32 :=
  let c := (old &&& 0xFFFFFFC0) ||| newMode.toUInt32
  let c := bitClear32 c 5
  let c := if maskI then bitSet32 c 7 else c
  if maskF then bitSet32 c 6 else c

end AGB
