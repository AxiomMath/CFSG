module

public import Certificates.Kernel.J2Dc.Data
public import Certificates.Data.Kernel.SporLatDcCode
public import Certificates.Data.Kernel.SporLatDcLin

public noncomputable section

namespace CFSG.KD.J2Dc

open CFSG.KC.SLDc CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def L0 (l : Nat) : Nat → Nat := CFSG.KC.LQT.PW.imgW J.tw (J.tc.getD l 0)

@[expose] def L (l : Nat) : Nat → Nat := pairF 315 (L0 l)

@[expose] def C : DcCtx := ⟨99225, J.delta, L, 6, 3, 7, 4725⟩

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

@[expose] def Δc : List Nat := [9181, 46785, 49325, 49444, 77491, 77498, 88867, 88874]

@[expose] def T (l : Nat) : Array Nat := (J.tabs.getD l []).toArray

@[expose] def sT : List (Array Nat) := [T 2, T 3, T 4]

@[expose] def mLet (j : Nat) : Array (Array Nat) :=
  (sT ++ (J.mw.getD j []).map (wordTabL #[T 0, T 1] 315)).toArray

@[expose] def Om (j : Nat) : OmegaData (List Nat) := omL (J.Om.getD j default)

@[expose] def memOK (j : Nat) : Bool := omCodeOK 315 (mLet j) Δc (Om j)

end CFSG.KD.J2Dc

end
