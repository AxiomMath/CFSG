module

public import Certificates.Kernel.M12Dc.Defs
public import Certificates.Kernel.M12Dc.OtData

public noncomputable section

namespace CFSG.KD.M12Dc

open CFSG.KC.SLDc CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def OtD (j : Nat) : OmegaData (List (List Nat)) := omL (JO.Ot.getD j default)

@[expose] def otOK (j : Nat) : Bool :=
  omOKG (fun l X => X.map (codeSetT 12 (sT.toArray.getD l #[]))) (Om j).lbl.toList 3 (OtD j)

@[expose] def m12OtK : Array (OmegaData (List (List ℕ))) := #[OtD 0, OtD 1, OtD 2]

end CFSG.KD.M12Dc

end
