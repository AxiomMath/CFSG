module

public import Certificates.Data.Kernel.Fi22Dc2.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.Fi22Dc2

@[expose] def r2c (i : Nat) : Bool := CFSG.KC.SLD2.rec2OK C D (Nat.add 22 i)

end CFSG.KD.Fi22Dc2

#kss_each CFSG.KD.Fi22Dc2.R2c CFSG.KD.Fi22Dc2.r2c 11

end
