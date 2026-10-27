module

public import Certificates.Kernel.R148Dc.J2BData
public import Certificates.Data.Kernel.SporLatDcCode

public noncomputable section

namespace CFSG.KD.R148Dc.J2B

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def L (l : Nat) : Nat → Nat := CFSG.KC.LQT.PW.imgW J.tw (J.tc.getD l 0)

@[expose] def C : DcCtx := ⟨315, J.delta, L, 8, 4, 0, 16800⟩

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

@[expose] def mE (j : Nat) : List (List Nat) := [[2], [3], [4], [5]] ++ J.mw.getD j []

@[expose] def Om (j : Nat) : OmegaData (List Nat) := omL (J.Om.getD j default)

@[expose] def memOK (j : Nat) : Bool :=
  omOKG (fun l x => labF (wordF L ((mE j).getD l [])) x) J.delta (mE j).length (Om j)

end CFSG.KD.R148Dc.J2B

end
