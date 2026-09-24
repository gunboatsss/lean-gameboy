/-
  LeanAGB.Proofs.Keypad — input mapping pins, KEYCNT interrupt
  contracts (OR/AND/enable), and button-application preservation.
  GBATEK "Keypad Input" numbers throughout.
-/
import LeanAGB.Sdl.Driver

namespace AGB

open AGB.Sdl

-- ── Host mask → KEYINPUT mapping ──

theorem buttons_released : buttonsToInput 0 = 0x3FF := by decide

theorem buttons_a : buttonsToInput 0x10 = 0x3FE := by decide

theorem buttons_start : buttonsToInput 0x80 = 0x3F7 := by decide

theorem buttons_ab : buttonsToInput 0x30 = 0x3FC := by decide

theorem buttons_l : buttonsToInput 0x400 = 0x1FF := by decide

theorem buttons_r : buttonsToInput 0x800 = 0x2FF := by decide

-- ── KEYCNT interrupt condition ──

theorem keyIrq_disabled : keyIrqFire 0x3FC 0 = false := by decide

theorem keyIrq_or_fire : keyIrqFire 0x3FE 0x4001 = true := by decide

theorem keyIrq_or_quiet : keyIrqFire 0x3FF 0x4001 = false := by decide

theorem keyIrq_or_empty_sel : keyIrqFire 0x3FC 0x4000 = false := by decide

theorem keyIrq_and_fire : keyIrqFire 0x3FC 0xC003 = true := by decide

theorem keyIrq_and_partial : keyIrqFire 0x3FE 0xC003 = false := by decide

-- ── Button application preserves machine state ──

theorem setButtons_cycles (s : AGBState) (mask : UInt32) :
    (setButtons s mask).cycles = s.cycles := by
  unfold setButtons
  simp only []
  repeat (first | split | rfl)

theorem setButtons_regs (s : AGBState) (mask : UInt32) :
    (setButtons s mask).regs = s.regs := by
  unfold setButtons
  simp only []
  repeat (first | split | rfl)

theorem setButtons_rom (s : AGBState) (mask : UInt32) :
    (setButtons s mask).rom = s.rom := by
  unfold setButtons
  simp only []
  repeat (first | split | rfl)

theorem setButtons_input (s : AGBState) (mask : UInt32) :
    (setButtons s mask).key.input = buttonsToInput mask := by
  rfl

end AGB
