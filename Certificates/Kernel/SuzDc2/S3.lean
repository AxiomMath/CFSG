module

public import Certificates.Kernel.SuzDc2.Slices
public import Certificates.Kernel.LocalComp.BlockGen

public noncomputable section

namespace CFSG.KD.SuzDc2

@[expose] def rs3 (j : Nat) : Bool := rowS 3 j

end CFSG.KD.SuzDc2

#lc_blocks CFSG.KD.SuzDc2.RS3 CFSG.KD.SuzDc2.rs3 10 1

end
