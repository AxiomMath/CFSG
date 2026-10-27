module

public import Certificates.Data.Kernel.Fi22Dc2.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.Fi22Dc2

@[expose] def r2a (i : Nat) : Bool := CFSG.KC.SLD2.rec2OK C D (Nat.add 0 i)

end CFSG.KD.Fi22Dc2

#kss_each CFSG.KD.Fi22Dc2.R2a CFSG.KD.Fi22Dc2.r2a 11

end
