/-
  LeanGameboy.Cpu.Decode — full SM83 opcode tables (512 opcodes).

  Decoding is data-first: `decode` / `decodeCB` map raw bytes to the
  `Instr` inductive. Cycle counts and lengths live next to the
  datatype so the executor and the proofs share one source of truth.
-/
import LeanGameboy.Basic

namespace GB

/-- Jump/call/return condition. -/
inductive Cond where
  | NZ | Z | NC | C
deriving DecidableEq, Repr

/-- 8-bit register operand (HLM = `(HL)`). -/
inductive R8 where
  | B | C | D | E | H | L | HLM | A
deriving DecidableEq, Repr

/-- 16-bit register pair operand (for LD/INC/DEC/ADD). -/
inductive R16 where
  | BC | DE | HL | SP
deriving DecidableEq, Repr

/-- Push/pop pair. -/
inductive RP where
  | BC | DE | HL | AF
deriving DecidableEq, Repr

/-- ALU operation. -/
inductive AluOp where
  | Add | Adc | Sub | Sbc | And | Xor | Or | Cp
deriving DecidableEq, Repr

/-- Rotate/shift operation (CB prefix). -/
inductive RotOp where
  | Rlc | Rrc | Rl | Rr | Sla | Sra | Swap | Srl
deriving DecidableEq, Repr

/-- Decoded instruction. Immediate operands are *not* stored here;
    the executor fetches them from the byte after the opcode. -/
inductive Instr where
  | Nop | Stop | Halt | Di | Ei | Reti
  | Daa | Cpl | Scf | Ccf
  | Rlca | Rrca | Rla | Rra
  | Invalid
  | LdR16Imm (r : R16)
  | LdMemR16BC | LdMemR16DE
  | LdMemHLI | LdMemHLD
  | LdA_MemR16BC | LdA_MemR16DE
  | LdA_MemHLI | LdA_MemHLD
  | IncR16 (r : R16) | DecR16 (r : R16)
  | AddHL (r : R16)
  | IncR8 (r : R8) | DecR8 (r : R8) | LdR8Imm (r : R8)
  | LdRR (dst src : R8)
  | Jr (c : Option Cond)
  | Jp (c : Option Cond) | JpHL
  | Call (c : Option Cond)
  | Ret (c : Option Cond)
  | Rst (vec : Nat)
  | Push (r : RP) | Pop (r : RP)
  | AluImm (op : AluOp) | AluR (op : AluOp) (r : R8)
  | LdMemNN_SP | LdMemNN_A | LdA_MemNN
  | LdhMem_A | LdhA_Mem | LdMemC_A | LdA_MemC
  | AddSP | LdHL_SP | LdSP_HL
  | Rot (op : RotOp) (r : R8)
  | Bit (b : Nat) (r : R8)
  | Res (b : Nat) (r : R8)
  | Set (b : Nat) (r : R8)
deriving DecidableEq, Repr

namespace Instr

/-- Decode register code 0..7 → R8. -/
def r8of : Nat → R8
  | 0 => .B | 1 => .C | 2 => .D | 3 => .E
  | 4 => .H | 5 => .L | 6 => .HLM | _ => .A

/-- Decode an unprefixed opcode byte. -/
def decode (x : UInt8) : Instr :=
  let hi := (x / 16).toNat
  let lo := (x % 16).toNat
  match hi, lo with
  | 0x0, 0x0 => .Nop
  | 0x0, 0x1 => .LdR16Imm .BC
  | 0x0, 0x2 => .LdMemR16BC
  | 0x0, 0x3 => .IncR16 .BC
  | 0x0, 0x4 => .IncR8 .B
  | 0x0, 0x5 => .DecR8 .B
  | 0x0, 0x6 => .LdR8Imm .B
  | 0x0, 0x7 => .Rlca
  | 0x0, 0x8 => .LdMemNN_SP
  | 0x0, 0x9 => .AddHL .BC
  | 0x0, 0xA => .LdA_MemR16BC
  | 0x0, 0xB => .DecR16 .BC
  | 0x0, 0xC => .IncR8 .C
  | 0x0, 0xD => .DecR8 .C
  | 0x0, 0xE => .LdR8Imm .C
  | 0x0, 0xF => .Rrca
  | 0x1, 0x0 => .Stop
  | 0x1, 0x1 => .LdR16Imm .DE
  | 0x1, 0x2 => .LdMemR16DE
  | 0x1, 0x3 => .IncR16 .DE
  | 0x1, 0x4 => .IncR8 .D
  | 0x1, 0x5 => .DecR8 .D
  | 0x1, 0x6 => .LdR8Imm .D
  | 0x1, 0x7 => .Rla
  | 0x1, 0x8 => .Jr none
  | 0x1, 0x9 => .AddHL .DE
  | 0x1, 0xA => .LdA_MemR16DE
  | 0x1, 0xB => .DecR16 .DE
  | 0x1, 0xC => .IncR8 .E
  | 0x1, 0xD => .DecR8 .E
  | 0x1, 0xE => .LdR8Imm .E
  | 0x1, 0xF => .Rra
  | 0x2, 0x0 => .Jr (.some .NZ)
  | 0x2, 0x1 => .LdR16Imm .HL
  | 0x2, 0x2 => .LdMemHLI
  | 0x2, 0x3 => .IncR16 .HL
  | 0x2, 0x4 => .IncR8 .H
  | 0x2, 0x5 => .DecR8 .H
  | 0x2, 0x6 => .LdR8Imm .H
  | 0x2, 0x7 => .Daa
  | 0x2, 0x8 => .Jr (.some .Z)
  | 0x2, 0x9 => .AddHL .HL
  | 0x2, 0xA => .LdA_MemHLI
  | 0x2, 0xB => .DecR16 .HL
  | 0x2, 0xC => .IncR8 .L
  | 0x2, 0xD => .DecR8 .L
  | 0x2, 0xE => .LdR8Imm .L
  | 0x2, 0xF => .Cpl
  | 0x3, 0x0 => .Jr (.some .NC)
  | 0x3, 0x1 => .LdR16Imm .SP
  | 0x3, 0x2 => .LdMemHLD
  | 0x3, 0x3 => .IncR16 .SP
  | 0x3, 0x4 => .IncR8 .HLM
  | 0x3, 0x5 => .DecR8 .HLM
  | 0x3, 0x6 => .LdR8Imm .HLM
  | 0x3, 0x7 => .Scf
  | 0x3, 0x8 => .Jr (.some .C)
  | 0x3, 0x9 => .AddHL .SP
  | 0x3, 0xA => .LdA_MemHLD
  | 0x3, 0xB => .DecR16 .SP
  | 0x3, 0xC => .IncR8 .A
  | 0x3, 0xD => .DecR8 .A
  | 0x3, 0xE => .LdR8Imm .A
  | 0x3, 0xF => .Ccf
  | 0x4, _ | 0x5, _ | 0x6, _ | 0x7, _ =>
    let v := (hi - 4) * 16 + lo
    if v == 0x36 then .Halt
    else .LdRR (r8of (v / 8)) (r8of (v % 8))
  | _, _ => .Invalid

/-- Fixed decoder used at runtime (total, table-driven by nibbles). -/
def decodeFull (x : UInt8) : Instr :=
  let n := x.toNat
  if n < 0x80 then decode x
  else if n < 0xC0 then
    let v := n - 0x80
    let op : AluOp :=
      match v / 8 with
      | 0 => .Add | 1 => .Adc | 2 => .Sub | 3 => .Sbc
      | 4 => .And | 5 => .Xor | 6 => .Or | _ => .Cp
    .AluR op (r8of (v % 8))
  else
    match n with
    | 0xC0 => .Ret (.some .NZ)
    | 0xC1 => .Pop .BC
    | 0xC2 => .Jp (.some .NZ)
    | 0xC3 => .Jp none
    | 0xC4 => .Call (.some .NZ)
    | 0xC5 => .Push .BC
    | 0xC6 => .AluImm .Add
    | 0xC7 => .Rst 0
    | 0xC8 => .Ret (.some .Z)
    | 0xC9 => .Ret none
    | 0xCA => .Jp (.some .Z)
    | 0xCC => .Call (.some .Z)
    | 0xCD => .Call none
    | 0xCE => .AluImm .Adc
    | 0xCF => .Rst 1
    | 0xD0 => .Ret (.some .NC)
    | 0xD1 => .Pop .DE
    | 0xD2 => .Jp (.some .NC)
    | 0xD4 => .Call (.some .NC)
    | 0xD5 => .Push .DE
    | 0xD6 => .AluImm .Sub
    | 0xD7 => .Rst 2
    | 0xD8 => .Ret (.some .C)
    | 0xD9 => .Reti
    | 0xDA => .Jp (.some .C)
    | 0xDC => .Call (.some .C)
    | 0xDE => .AluImm .Sbc
    | 0xDF => .Rst 3
    | 0xE0 => .LdhMem_A
    | 0xE1 => .Pop .HL
    | 0xE2 => .LdMemC_A
    | 0xE5 => .Push .HL
    | 0xE6 => .AluImm .And
    | 0xE7 => .Rst 4
    | 0xE8 => .AddSP
    | 0xE9 => .JpHL
    | 0xEA => .LdMemNN_A
    | 0xEE => .AluImm .Xor
    | 0xEF => .Rst 5
    | 0xF0 => .LdhA_Mem
    | 0xF1 => .Pop .AF
    | 0xF2 => .LdA_MemC
    | 0xF3 => .Di
    | 0xF5 => .Push .AF
    | 0xF6 => .AluImm .Or
    | 0xF7 => .Rst 6
    | 0xF8 => .LdHL_SP
    | 0xF9 => .LdSP_HL
    | 0xFA => .LdA_MemNN
    | 0xFB => .Ei
    | 0xFE => .AluImm .Cp
    | 0xFF => .Rst 7
    | _ => .Invalid

/-- Decode a CB-prefixed second byte. -/
def decodeCB (x : UInt8) : Instr :=
  let n := x.toNat
  let grp := n / 8
  let r := r8of (n % 8)
  match grp with
  | 0 => .Rot .Rlc r
  | 1 => .Rot .Rrc r
  | 2 => .Rot .Rl r
  | 3 => .Rot .Rr r
  | 4 => .Rot .Sla r
  | 5 => .Rot .Sra r
  | 6 => .Rot .Swap r
  | 7 => .Rot .Srl r
  | g =>
    let b := (g - 8) % 8
    if g < 16 then .Bit b r
    else if g < 24 then .Res b r
    else .Set b r

/-- Instruction length in bytes (including immediates). -/
def len : Instr → Nat
  | .LdR16Imm _ => 3 | .Jr _ => 2
  | .Jp none => 3 | .Jp (.some _) => 3
  | .Call _ => 3 | .Rst _ => 1
  | .AluImm _ => 2 | .LdR8Imm _ => 2
  | .LdMemNN_SP => 3 | .LdMemNN_A => 3 | .LdA_MemNN => 3
  | .LdhMem_A => 2 | .LdhA_Mem => 2
  | .AddSP => 2 | .LdHL_SP => 2
  | .Rot _ _ => 2 | .Bit _ _ => 2 | .Res _ _ => 2 | .Set _ _ => 2
  | _ => 1

/-- Base M-cycles (conditional branches/calls add extra when taken). -/
def baseCycles : Instr → Nat
  | .LdR16Imm _ => 3 | .Jr _ => 2
  | .Jp none => 4 | .Jp (.some _) => 3
  | .JpHL => 1 | .Call _ => 3 | .Ret _ => 2 | .Reti => 4
  | .Rst _ => 4 | .Push _ => 4 | .Pop _ => 3
  | .AluImm _ => 2 | .AddSP => 4 | .LdHL_SP => 3
  | .LdMemNN_SP => 5 | .LdMemNN_A => 4 | .LdA_MemNN => 4
  | .LdhMem_A => 3 | .LdhA_Mem => 3 | .LdMemC_A => 2 | .LdA_MemC => 2
  | .LdSP_HL => 2 | .Halt => 1 | .Stop => 1
  | .Rot _ .HLM => 4 | .Rot _ _ => 2
  | .Bit _ .HLM => 3 | .Bit _ _ => 2
  | .Res _ .HLM => 4 | .Res _ _ => 2
  | .Set _ .HLM => 4 | .Set _ _ => 2
  | .LdRR .HLM _ => 2 | .LdRR _ .HLM => 2 | .LdRR _ _ => 1
  | .AluR _ .HLM => 2 | .AluR _ _ => 1
  | .IncR8 .HLM => 3 | .DecR8 .HLM => 3
  | .IncR8 _ => 1 | .DecR8 _ => 1 | .LdR8Imm .HLM => 3 | .LdR8Imm _ => 2
  | .AddHL _ => 2 | .IncR16 _ => 2 | .DecR16 _ => 2
  | .LdMemR16BC => 2 | .LdMemR16DE => 2
  | .LdMemHLI => 2 | .LdMemHLD => 2
  | .LdA_MemR16BC => 2 | .LdA_MemR16DE => 2
  | .LdA_MemHLI => 2 | .LdA_MemHLD => 2
  | _ => 1

end Instr

end GB
