module

public import Certificates.Kernel.SuzDc2.Slices
public import Certificates.Kernel.LocalComp.BlockGen

public noncomputable section

namespace CFSG.KD.SuzDc2

@[expose] def rs1 (j : Nat) : Bool := rowS 1 j

end CFSG.KD.SuzDc2

#lc_blocks CFSG.KD.SuzDc2.RS1 CFSG.KD.SuzDc2.rs1 10 1

end
