module

public import Certificates.Kernel.M11Dc.Defs
public import CFSG.Quasithin.Vol2.KGFactSporLatInputs
public import CFSG.Certificates.Kernel.E64FSound

public noncomputable section

namespace CFSG.KD.M11Dc

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Quasithin.H13.KGSporLat

@[expose] def m11LatK : LatData (List ℕ) where
  O := default
  F := default
  sTabs := m11STabs
  mw := J.mw.toArray
  mt := J.mw.toArray.map fun ws => ws.map (CFSG.KC.SLDc.wordTabL #[m11ta.toArray, m11tb.toArray] 11)
  Om := #[Om 0, Om 1, Om 2, Om 3]
  atoms := #[]
  joins := []

@[expose] def m11OtK : Array (OmegaData (List (List ℕ))) := #[OtD 0, OtD 1, OtD 2, OtD 3]

theorem delta_eq : m11Delta = Δc := by
  rw [m11Delta, CFSG.KC.E64F.sortN_eq]
  decide

end CFSG.KD.M11Dc

end
