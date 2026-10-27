module

public import Certificates.Kernel.M23Dc.Defs
public import Certificates.Kernel.M23Dc.OtData
public import Certificates.Data.Kernel.SporLatDcTup

public noncomputable section

namespace CFSG.KD.M23Dc

open CFSG.KC.SLDc CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def OtI (j : Nat) : OmegaData (List Nat) := omL (JO.Ot.getD j default)

@[expose] def Ps (j : Nat) : List Nat := ((oc j).2.1.take 3).map (CFSG.KC.LQT.PP.codeK 12)

@[expose] def otOK (j : Nat) : Bool := otIdxOK 12 (oc j).1.flatten.length (Ps j) (OtI j)

end CFSG.KD.M23Dc

end
