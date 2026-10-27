module

public import Certificates.Kernel.M22Dc.Defs
public import Certificates.Kernel.M22Dc.OtData

public noncomputable section

namespace CFSG.KD.M22Dc

open CFSG.KC.SLDc CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def OtD (j : Nat) : OmegaData (List (List Nat)) := omL (JO.Ot.getD j default)

@[expose] def otOK (j : Nat) : Bool :=
  omOKG (fun l X => X.map (codeSetT 22 (sT.toArray.getD l #[]))) (Om j).lbl.toList 3 (OtD j)

@[expose] def m22OtK : Array (OmegaData (List (List ℕ))) := #[OtD 0, OtD 1, OtD 2, OtD 3, OtD 4]

end CFSG.KD.M22Dc

end
