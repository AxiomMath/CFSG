module

public import Certificates.Data.Kernel.Fi22Dc2.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.Fi22Dc2

@[expose] def fr0 (i : Nat) : Bool := CFSG.KC.SLD2.fRowOK C D (Nat.add 0 i)

end CFSG.KD.Fi22Dc2

#kss_each CFSG.KD.Fi22Dc2.F0 CFSG.KD.Fi22Dc2.fr0 3

end
