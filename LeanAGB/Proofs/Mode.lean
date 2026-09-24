/-
  LeanAGB.Proofs.Mode — exception/model-state contracts: mode-number
  codec, bank isolation (a bank write is invisible outside its mode,
  visible inside it), exception-entry field preservation, and the
  SVC/IRQ entry→return round trips on concrete states.
-/
import LeanAGB.Bus

namespace AGB

-- ── Mode-number codec ──

theorem mode_fiq_n : MODE_FIQ.toNat = 0x11 := by decide
theorem mode_irq_n : MODE_IRQ.toNat = 0x12 := by decide
theorem mode_svc_n : MODE_SVC.toNat = 0x13 := by decide
theorem mode_abt_n : MODE_ABT.toNat = 0x17 := by decide
theorem mode_und_n : MODE_UND.toNat = 0x1B := by decide
theorem mode_sys_n : MODE_SYS.toNat = 0x1F := by decide

theorem cpsrMode_sys : cpsrMode 0x3F = 0x1F := by decide
theorem cpsrMode_irq : cpsrMode 0x92 = 0x12 := by decide
theorem cpsrMode_svc : cpsrMode 0x93 = 0x13 := by decide

-- ── Exception CPSR surgery values ──

theorem excCpsr_irq_val : excCpsr 0x3F MODE_IRQ true false = 0x92 := by decide

theorem excCpsr_svc_val : excCpsr 0x3F MODE_SVC false false = 0x13 := by decide

-- ── Entry field preservation (structural) ──

theorem serviceIrq_ime_off (s : AGBState) : (serviceIrq s).irq.ime = false := by
  rfl

theorem serviceIrq_cpsr (s : AGBState) :
    (serviceIrq s).regs.cpsr = excCpsr s.regs.cpsr MODE_IRQ true false := by
  rfl

theorem serviceIrq_spsr (s : AGBState) :
    (serviceIrq s).regs.spsr_irq = s.regs.cpsr := by
  rfl

theorem serviceIrq_lr (s : AGBState) :
    (serviceIrq s).regs.r14_irq = s.regs.pc + 4 := by
  rfl

theorem serviceSwi_cpsr (s : AGBState) (a : UInt32) :
    (serviceSwi s a).regs.cpsr = excCpsr s.regs.cpsr MODE_SVC false false := by
  rfl

theorem serviceSwi_spsr (s : AGBState) (a : UInt32) :
    (serviceSwi s a).regs.spsr_svc = s.regs.cpsr := by
  rfl

theorem serviceSwi_lr (s : AGBState) (a : UInt32) :
    (serviceSwi s a).regs.r14_svc = a + 4 := by
  rfl

theorem excReturn_cpsr (s : AGBState) (p l : UInt32) :
    (excReturn s p l).regs.cpsr = p := by
  rfl

theorem excReturn_cycles (s : AGBState) (p l : UInt32) :
    (excReturn s p l).cycles = s.cycles := by
  rfl

-- ── Bank isolation: writes are invisible outside their mode ──

theorem get13_sys_ignores_irq (rs : ArmRegs) (v : UInt32)
    (h : cpsrMode rs.cpsr = 0x1F) :
    ({ rs with r13_irq := v }.get 13) = rs.get 13 := by
  unfold ArmRegs.get
  simp [h, mode_fiq_n, mode_irq_n, mode_svc_n, mode_abt_n, mode_und_n]

theorem get14_sys_ignores_svc (rs : ArmRegs) (v : UInt32)
    (h : cpsrMode rs.cpsr = 0x1F) :
    ({ rs with r14_svc := v }.get 14) = rs.get 14 := by
  unfold ArmRegs.get
  simp [h, mode_fiq_n, mode_irq_n, mode_svc_n, mode_abt_n, mode_und_n]

theorem get8_sys_ignores_fiq (rs : ArmRegs) (a : Array UInt32)
    (h : cpsrMode rs.cpsr = 0x1F) :
    ({ rs with fiqHi := a }.get 8) = rs.get 8 := by
  unfold ArmRegs.get
  simp [h, mode_fiq_n]

-- ── ... and visible inside it ──

theorem get13_irq_sees_bank (rs : ArmRegs) (v : UInt32) :
    ({ rs with cpsr := 0x92, r13_irq := v }.get 13) = v := by
  unfold ArmRegs.get
  simp [cpsrMode_irq, mode_fiq_n, mode_irq_n]

theorem get14_svc_sees_bank (rs : ArmRegs) (v : UInt32) :
    ({ rs with cpsr := 0x93, r14_svc := v }.get 14) = v := by
  unfold ArmRegs.get
  simp [cpsrMode_svc, mode_fiq_n, mode_irq_n, mode_svc_n]

-- ── SVC entry → handler return round trip (concrete) ──

/-- SYS-mode state with PC installed (16 GPRs). -/
def excTest (pc : UInt32) : AGBState :=
  { ({} : AGBState) with
    regs := { r := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, pc],
              cpsr := 0x3F } }

theorem svc_entry_mode :
    cpsrMode (serviceSwi (excTest 0x08000100) 0x08000100).regs.cpsr = 0x13 := by
  decide

theorem svc_entry_spsr :
    (serviceSwi (excTest 0x08000100) 0x08000100).regs.spsr_svc = 0x3F := by
  decide

theorem svc_entry_lr :
    (serviceSwi (excTest 0x08000100) 0x08000100).regs.r14_svc = 0x08000104 := by
  decide

theorem svc_entry_vec :
    (serviceSwi (excTest 0x08000100) 0x08000100).regs.pc = 0x08 := by
  decide

theorem svc_roundtrip_cpsr :
    (excReturn (serviceSwi (excTest 0x08000100) 0x08000100)
      ((serviceSwi (excTest 0x08000100) 0x08000100).regs.spsr_svc)
      ((serviceSwi (excTest 0x08000100) 0x08000100).regs.r14_svc)).regs.cpsr
      = 0x3F := by
  decide

theorem svc_roundtrip_pc :
    (excReturn (serviceSwi (excTest 0x08000100) 0x08000100)
      ((serviceSwi (excTest 0x08000100) 0x08000100).regs.spsr_svc)
      ((serviceSwi (excTest 0x08000100) 0x08000100).regs.r14_svc)).regs.pc
      = 0x08000104 := by
  decide

-- ── IRQ entry pins (concrete) ──

theorem irq_entry_mode :
    cpsrMode (serviceIrq (excTest 0x08000100)).regs.cpsr = 0x12 := by
  decide

theorem irq_entry_ime :
    (serviceIrq (excTest 0x08000100)).irq.ime = false := by
  decide

theorem irq_entry_spsr :
    (serviceIrq (excTest 0x08000100)).regs.spsr_irq = 0x3F := by
  decide

theorem irq_entry_lr :
    (serviceIrq (excTest 0x08000100)).regs.r14_irq = 0x08000104 := by
  decide

theorem irq_entry_vec :
    (serviceIrq (excTest 0x08000100)).regs.pc = 0x18 := by
  decide

end AGB
