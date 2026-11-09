module

public import Certificates.Kernel.R148Dc.M22CData
public import Certificates.Data.Kernel.SporLatDcCode

public noncomputable section

namespace CFSG.KD.R148Dc.M22C

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def m22cPT : Nat := 7423048125848207811658833542040524899110788223353415115150327486868628003907924830175997951351168588000603548500090022537482767487534790429410693455507557697252648555767448036047629867693057205945468461226461647803588454852404959860550065171467083205176933182344483421578350312598567851451412805210251932643673022770686890445487340

@[expose] def L0 (l : Nat) : Nat → Nat := fun p =>
  Nat.mod (Nat.shiftRight m22cPT (Nat.mul 5 (Nat.add (Nat.mul 22 l) p))) 32

@[expose] def L (l : Nat) : Nat → Nat := pairF 22 (L0 l)

@[expose] def C : DcCtx := ⟨484, J.delta, L, 8, 4, 0, 12320⟩

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

end CFSG.KD.R148Dc.M22C

end
