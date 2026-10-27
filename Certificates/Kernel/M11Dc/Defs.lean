module

public import Certificates.Kernel.M11Dc.Data
public import Certificates.Data.Kernel.SporLatDcCode

public noncomputable section

namespace CFSG.KD.M11Dc

open CFSG.KC.SLDc CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def L0 (l : Nat) : Nat → Nat := tabF (J.tabs.getD l [])

@[expose] def L (l : Nat) : Nat → Nat := pairF 11 (L0 l)

@[expose] def C : DcCtx := ⟨121, J.delta, L, 4, 2, 4, 495⟩

@[expose] def D : DcData where
  w := J.w
  oidC := J.oidC
  tlC := J.tlC
  dpC := J.dpC
  obase := J.obase
  osz := J.osz
  K := J.K
  sep := J.sep
  mw := J.mw
  Rc := [J.R0]
  msum := J.msum
  joins := J.joins
  csz := J.csz
  c0 := J.c0
  pcz := J.pcz
  npc := J.npc

@[expose] def Δc : List Nat := [25, 38, 50, 62, 86, 98, 122, 134]

@[expose] def T (l : Nat) : Array Nat := (J.tabs.getD l []).toArray

@[expose] def sT : List (Array Nat) := [T 2, T 3]

@[expose] def mLet (j : Nat) : Array (Array Nat) :=
  (sT ++ (J.mw.getD j []).map (wordTabL #[T 0, T 1] 11)).toArray

@[expose] def Om (j : Nat) : OmegaData (List Nat) := omL (J.Om.getD j default)

@[expose] def memOK (j : Nat) : Bool := omCodeOK 11 (mLet j) Δc (Om j)

@[expose] def OtD (j : Nat) : OmegaData (List (List Nat)) := omL (J.Ot.getD j default)

@[expose] def otOK (j : Nat) : Bool :=
  omOKG (fun l X => X.map (codeSetT 11 (sT.toArray.getD l #[]))) (Om j).lbl.toList 2 (OtD j)

end CFSG.KD.M11Dc

end
