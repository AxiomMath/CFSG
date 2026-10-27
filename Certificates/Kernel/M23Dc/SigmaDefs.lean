module

public import Certificates.Kernel.M23Dc.Lit
public import Certificates.Data.Kernel.SporLatSigmaL
public import Certificates.Data.Kernel.E64L

public noncomputable section

namespace CFSG.KD.M23Dc

open CFSG.KC.SLDc CFSG.KC.SLSig CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def m23LatS : LatData (List ℕ) where
  O := default
  F := default
  sTabs := sT
  mw := J.mw.toArray
  mt := (J.mw.map fun ws => ws.map (wordTabL #[T 0, T 1] 23)).toArray
  Om := #[Om 0, Om 1, Om 2, Om 3, Om 4, Om 5, Om 6, Om 7, Om 8, Om 9, Om 10, Om 11, Om 12, Om 13,
    Om 14, Om 15]
  atoms := #[]
  joins := []

@[expose] def lblK (j : Nat) : List (List Nat) := (oc j).1.flatten

@[expose] def gK (j jj : Nat) : Bool :=
  gensInL (codeSetT 23) Δc ((J.mw.getD j []).map (wordTabL #[T 0, T 1] 23)) (lblK jj)

@[expose] def sigK (j : Nat) : Bool :=
  sigmaCheckL (CFSG.KC.E64L.codeSetTL 23) 23 Δc m23LatS lblK [j] [4, 6, 10, 11, 12, 13, 14]

end CFSG.KD.M23Dc

end
