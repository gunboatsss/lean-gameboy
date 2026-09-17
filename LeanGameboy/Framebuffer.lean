/-
  LeanGameboy.Framebuffer — 160×144 RGB framebuffer + PPM dumps.
-/
import LeanGameboy.Basic

namespace GB

def fbWidth : Nat := 160
def fbHeight : Nat := 144

/-- Classic DMG green palette (ARGB). -/
def dmgShade : Nat → UInt32
  | 0 => 0xFF9BBC0F
  | 1 => 0xFF8BAC0F
  | 2 => 0xFF306230
  | _ => 0xFF0F380F

/-- Blank framebuffer. -/
def fbBlank : Array UInt32 :=
  Array.mk (List.replicate (fbWidth * fbHeight) 0xFF9BBC0F)

/-- Write one pixel. -/
def fbSet (fb : Array UInt32) (x y : Nat) (c : UInt32) : Array UInt32 :=
  if x < fbWidth && y < fbHeight then fb.set! (y * fbWidth + x) c
  else fb

/-- Blit one rendered scanline of final shade indices (0..3). -/
def fbBlitLine (fb : Array UInt32) (ly : Nat) (line : Array Nat) : Array UInt32 :=
  let rec loop (x : Nat) (acc : Array UInt32) : Array UInt32 :=
    if x >= fbWidth then acc
    else
      let shade := if x < line.size then line[x]! % 4 else 0
      loop (x + 1) (fbSet acc x ly (dmgShade shade))
  loop 0 fb

/-- Dump the framebuffer as a binary P6 PPM (`headless --dump` path). -/
def fbToPPM (fb : Array UInt32) : ByteArray :=
  let header : Array UInt8 :=
    "P6\n160 144\n255\n".toList.toArray.map (fun c => w8 c.toNat)
  let px (c : UInt32) : Array UInt8 :=
    #[w8 ((c >>> 16).toNat % 256), w8 ((c >>> 8).toNat % 256), w8 (c.toNat % 256)]
  let body := (List.range (fbWidth * fbHeight)).foldl
    (fun acc i => acc ++ px (if i < fb.size then fb[i]! else 0)) #[]
  ByteArray.mk (header ++ body)
