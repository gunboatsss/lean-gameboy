/- LeanAGB.Keypad — KEYINPUT (active-low) + KEYCNT interrupt.
   GBATEK "Keypad Input": KEYCNT bits 0-9 select buttons, bit 14 IRQ
   enable, bit 15 condition (0 = OR/any selected pressed, 1 = AND/all
   selected pressed); fires IF.12. R/L have no host keys (stay put). -/
namespace AGB
structure AgbKeypad where
  input : UInt16 := 0x3FF  -- all released (active-low)
  cnt : UInt16 := 0
deriving DecidableEq, Repr

/-- KEYCNT interrupt condition for the current input state. -/
def keyIrqFire (input cnt : UInt16) : Bool :=
  if ((cnt.toNat >>> 14) &&& 1) == 0 then false
  else
    let pressed := (0x3FF ^^^ (input.toNat &&& 0x3FF)) &&& 0x3FF
    let sel := cnt.toNat &&& 0x3FF
    if ((cnt.toNat >>> 15) &&& 1) == 1 then
      sel != 0 && (pressed &&& sel) == sel
    else (pressed &&& sel) != 0
end AGB
