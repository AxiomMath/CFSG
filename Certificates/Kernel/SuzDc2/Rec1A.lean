module

public import Certificates.Data.Kernel.SuzDc2.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import Certificates.Kernel.LocalComp.BlockGen

public noncomputable section

namespace CFSG.KD.SuzDc2

@[expose] def r1a (c : Nat) : Bool := CFSG.KC.SLD2.rec1OK C D (D.R1.getD (Nat.add 0 c) default)

end CFSG.KD.SuzDc2

#lc_blocks CFSG.KD.SuzDc2.R1A CFSG.KD.SuzDc2.r1a 25 1

end
