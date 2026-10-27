module

public import Certificates.Kernel.J2Dc.Defs
public import CFSG.Quasithin.Background.E2TwoProofSporJ2Inputs
public import CFSG.Certificates.Kernel.E64FSound

public noncomputable section

namespace CFSG.KD.J2Dc

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Quasithin.E2P.SporB.J2Lat

@[expose] def j2LatK : LatData (List ℕ) where
  O := default
  F := default
  sTabs := j2STabs
  mw := J.mw.toArray
  mt := J.mw.toArray.map fun ws =>
    ws.map (CFSG.KC.SLDc.wordTabL #[j2ta.toArray, j2tb.toArray] 315)
  Om := #[Om 0, Om 1, Om 2, Om 3, Om 4]
  atoms := #[]
  joins := []

theorem delta_eq : j2Delta = Δc := by
  rw [j2Delta, CFSG.KC.E64F.sortN_eq]
  decide

end CFSG.KD.J2Dc

end
