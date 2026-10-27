module

public import Certificates.Data.Kernel.SuzDc2.Defs
public import Certificates.Kernel.LocalComp.BlockGen

public noncomputable section

namespace CFSG.KD.SuzDc2

@[expose] def w1 (p : Nat) : Bool :=
  Nat.beq (L 1 p) (CFSG.KC.E64F.wordF L (LT.sgw.getD 1 []) p)

end CFSG.KD.SuzDc2

#lc_blocks CFSG.KD.SuzDc2.W1B CFSG.KD.SuzDc2.w1 22880 1907

end
