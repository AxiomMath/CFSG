module

public import Certificates.Kernel.M22Dc.Defs
public import CFSG.Quasithin.Background.HSporLatInputs
public import CFSG.Certificates.Kernel.E64FSound

public noncomputable section

namespace CFSG.KD.M22Dc

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Quasithin.H.MathieuLat

@[expose] def m22LatK : LatData (List ℕ) where
  O := default
  F := default
  sTabs := m22STabs
  mw := J.mw.toArray
  mt := J.mw.toArray.map fun ws => ws.map (CFSG.KC.SLDc.wordTabL #[m22ta.toArray, m22tb.toArray] 22)
  Om := #[Om 0, Om 1, Om 2, Om 3, Om 4]
  atoms := #[]
  joins := []

theorem delta_eq : m22Delta = Δc := by
  rw [m22Delta, CFSG.KC.E64F.sortN_eq]
  decide

end CFSG.KD.M22Dc

end
