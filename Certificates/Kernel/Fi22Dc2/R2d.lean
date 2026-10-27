module

public import Certificates.Data.Kernel.Fi22Dc2.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.Fi22Dc2

@[expose] def r2d (i : Nat) : Bool := CFSG.KC.SLD2.rec2OK C D (Nat.add 33 i)

end CFSG.KD.Fi22Dc2

#kss_each CFSG.KD.Fi22Dc2.R2d CFSG.KD.Fi22Dc2.r2d 12

end
