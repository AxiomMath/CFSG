module

public import Certificates.Data.Kernel.McLDc2.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import Certificates.Kernel.LocalComp.BlockGen

public noncomputable section

namespace CFSG.KD.McLDc2

@[expose] def rt2 (b : Nat) : Bool := CFSG.KC.SLD2.rootsOK C D (Nat.add 150 b)

end CFSG.KD.McLDc2

#lc_blocks CFSG.KD.McLDc2.RB2 CFSG.KD.McLDc2.rt2 70 5

end
