module

public import Certificates.Kernel.SuzDc2.Slices
public import Certificates.Kernel.LocalComp.BlockGen

public noncomputable section

namespace CFSG.KD.SuzDc2

@[expose] def rs2 (j : Nat) : Bool := rowS 2 j

end CFSG.KD.SuzDc2

#lc_blocks CFSG.KD.SuzDc2.RS2 CFSG.KD.SuzDc2.rs2 10 1

end
