module

public import Certificates.Kernel.M12Dc.Defs
public import CFSG.Quasithin.Background.HSporLatInputs
public import CFSG.Certificates.Kernel.E64FSound

public noncomputable section

namespace CFSG.KD.M12Dc

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Quasithin.H.MathieuLat

@[expose] def m12LatK : LatData (List ℕ) where
  O := default
  F := default
  sTabs := m12STabs
  mw := J.mw.toArray
  mt := J.mw.toArray.map fun ws => ws.map (CFSG.KC.SLDc.wordTabL #[m12ta.toArray, m12tb.toArray] 12)
  Om := #[Om 0, Om 1, Om 2]
  atoms := #[]
  joins := []

theorem delta_eq : m12Delta = Δc := by
  rw [m12Delta, CFSG.KC.E64F.sortN_eq]
  decide

end CFSG.KD.M12Dc

end
