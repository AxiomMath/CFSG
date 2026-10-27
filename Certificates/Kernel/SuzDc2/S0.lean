module

public import Certificates.Kernel.SuzDc2.Slices
public import Certificates.Kernel.LocalComp.BlockGen

public noncomputable section

namespace CFSG.KD.SuzDc2

@[expose] def rs0 (j : Nat) : Bool := rowS 0 j

end CFSG.KD.SuzDc2

#lc_blocks CFSG.KD.SuzDc2.RS0 CFSG.KD.SuzDc2.rs0 10 1

end
