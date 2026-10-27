module

public import Certificates.Data.Kernel.SuzDc2.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import Certificates.Kernel.LocalComp.BlockGen

public noncomputable section

namespace CFSG.KD.SuzDc2

@[expose] def r1c (c : Nat) : Bool := CFSG.KC.SLD2.rec1OK C D (D.R1.getD (Nat.add 45 c) default)

end CFSG.KD.SuzDc2

#lc_blocks CFSG.KD.SuzDc2.R1C CFSG.KD.SuzDc2.r1c 30 1

end
