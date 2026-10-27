module

public import Certificates.Data.Kernel.Fi22Dc2.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.Fi22Dc2

@[expose] def rtb (i : Nat) : Bool := CFSG.KC.SLD2.rootsOK C D i

end CFSG.KD.Fi22Dc2

#kss_each CFSG.KD.Fi22Dc2.RT CFSG.KD.Fi22Dc2.rtb 73

end
