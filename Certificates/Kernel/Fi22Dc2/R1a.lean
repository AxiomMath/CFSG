module

public import Certificates.Data.Kernel.Fi22Dc2.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.Fi22Dc2

@[expose] def r1a (i : Nat) : Bool := CFSG.KC.SLD2.rec1OK C D (D.R1.getD (Nat.add 0 i) default)

end CFSG.KD.Fi22Dc2

#kss_each CFSG.KD.Fi22Dc2.R1a CFSG.KD.Fi22Dc2.r1a 15

end
