module

public import Certificates.Data.Kernel.SuzDc2.Defs
public import Certificates.Kernel.LocalComp.BlockGen

public noncomputable section

namespace CFSG.KD.SuzDc2

@[expose] def w3 (p : Nat) : Bool :=
  Nat.beq (L 3 p) (CFSG.KC.E64F.wordF L (LT.sgw.getD 3 []) p)

end CFSG.KD.SuzDc2

#lc_blocks CFSG.KD.SuzDc2.W3B CFSG.KD.SuzDc2.w3 22880 1760

end
