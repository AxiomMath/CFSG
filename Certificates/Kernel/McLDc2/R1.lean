module

public import Certificates.Data.Kernel.McLDc2.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import Certificates.Kernel.LocalComp.BlockGen

public noncomputable section

namespace CFSG.KD.McLDc2

@[expose] def rt1 (b : Nat) : Bool := CFSG.KC.SLD2.rootsOK C D (Nat.add 75 b)

end CFSG.KD.McLDc2

#lc_blocks CFSG.KD.McLDc2.RB1 CFSG.KD.McLDc2.rt1 75 5

end
