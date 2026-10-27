module

public import Certificates.Data.Kernel.SuzDc2.Defs
public import Certificates.Kernel.LocalComp.BlockGen

public noncomputable section

namespace CFSG.KD.SuzDc2

@[expose] def w2 (p : Nat) : Bool :=
  Nat.beq (L 2 p) (CFSG.KC.E64F.wordF L (LT.sgw.getD 2 []) p)

end CFSG.KD.SuzDc2

#lc_blocks CFSG.KD.SuzDc2.W2B CFSG.KD.SuzDc2.w2 22880 1635

end
