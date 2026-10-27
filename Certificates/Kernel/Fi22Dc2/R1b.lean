module

public import Certificates.Data.Kernel.Fi22Dc2.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.Fi22Dc2

@[expose] def r1b (i : Nat) : Bool := CFSG.KC.SLD2.rec1OK C D (D.R1.getD (Nat.add 15 i) default)

end CFSG.KD.Fi22Dc2

#kss_each CFSG.KD.Fi22Dc2.R1b CFSG.KD.Fi22Dc2.r1b 30

end
