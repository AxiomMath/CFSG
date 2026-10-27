module

public import Certificates.Kernel.SuzDc2.Slices
public import Certificates.Kernel.LocalComp.BlockGen

public noncomputable section

namespace CFSG.KD.SuzDc2

@[expose] def rs4 (j : Nat) : Bool := rowS 4 j

end CFSG.KD.SuzDc2

#lc_blocks CFSG.KD.SuzDc2.RS4 CFSG.KD.SuzDc2.rs4 10 1

end
