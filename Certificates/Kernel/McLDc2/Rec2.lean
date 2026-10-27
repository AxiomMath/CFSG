module

public import Certificates.Data.Kernel.McLDc2.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import Certificates.Kernel.LocalComp.BlockGen

public noncomputable section

namespace CFSG.KD.McLDc2

@[expose] def r2 (c : Nat) : Bool := CFSG.KC.SLD2.rec2OK C D c

end CFSG.KD.McLDc2

#lc_blocks CFSG.KD.McLDc2.R2B CFSG.KD.McLDc2.r2 302 16

end
