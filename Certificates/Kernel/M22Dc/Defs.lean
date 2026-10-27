module

public import Certificates.Kernel.M22Dc.Data
public import Certificates.Data.Kernel.SporLatDcCode

public noncomputable section

namespace CFSG.KD.M22Dc

open CFSG.KC.SLDc CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def L0 (l : Nat) : Nat → Nat := tabF (J.tabs.getD l [])

@[expose] def L (l : Nat) : Nat → Nat := pairF 22 (L0 l)

@[expose] def C : DcCtx := ⟨484, J.delta, L, 6, 3, 7, 3465⟩

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

@[expose] def Δc : List Nat := [280, 451, 494, 262112, 6107293000421346949332]

@[expose] def T (l : Nat) : Array Nat := (J.tabs.getD l []).toArray

@[expose] def sT : List (Array Nat) := [T 2, T 3, T 4]

@[expose] def mLet (j : Nat) : Array (Array Nat) :=
  (sT ++ (J.mw.getD j []).map (wordTabL #[T 0, T 1] 22)).toArray

@[expose] def Om (j : Nat) : OmegaData (List Nat) := omL (J.Om.getD j default)

@[expose] def memOK (j : Nat) : Bool := omCodeOK 22 (mLet j) Δc (Om j)

end CFSG.KD.M22Dc

end
