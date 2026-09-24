/- LeanAGB.Dma — 4-channel DMA stub (copies accounted in Bus.advance). -/
namespace AGB
structure DmaCh where
  sad : UInt32 := 0
  dad : UInt32 := 0
  cnt_l : UInt16 := 0
  cnt_h : UInt16 := 0
deriving DecidableEq, Repr
structure AgbDma where
  ch : Array DmaCh := Array.replicate 4 {}
deriving DecidableEq, Repr
end AGB
