module

public import Certificates.Kernel.M23Dc.Defs
public import CFSG.Quasithin.Background.HSporLatInputs
public import CFSG.Certificates.Kernel.E64FSound

public noncomputable section

namespace CFSG.KD.M23Dc

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Quasithin.H.MathieuLat

@[expose] def Om (j : Nat) : OmegaData (List ℕ) :=
  CFSG.KC.SLDc.omOf (oc j).1 (oc j).2.1 (oc j).2.2.1 (oc j).2.2.2.1

@[expose] def m23LatK : LatData (List ℕ) where
  O := default
  F := default
  sTabs := m23STabs
  mw := J.mw.toArray
  mt := J.mw.toArray.map fun ws => ws.map (CFSG.KC.SLDc.wordTabL #[m23ta.toArray, m23tb.toArray] 23)
  Om := #[Om 0, Om 1, Om 2, Om 3, Om 4, Om 5, Om 6, Om 7, Om 8, Om 9, Om 10, Om 11, Om 12, Om 13,
    Om 14, Om 15]
  atoms := #[]
  joins := []

theorem delta_eq : m23Delta = Δc := by
  rw [m23Delta, CFSG.KC.E64F.sortN_eq]
  decide

end CFSG.KD.M23Dc

end
