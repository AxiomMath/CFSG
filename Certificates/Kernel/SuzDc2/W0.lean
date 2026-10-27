module

public import Certificates.Data.Kernel.SuzDc2.Defs
public import Certificates.Kernel.LocalComp.BlockGen

public noncomputable section

namespace CFSG.KD.SuzDc2

@[expose] def w0 (p : Nat) : Bool :=
  Nat.beq (L 0 p) (CFSG.KC.E64F.wordF L (LT.sgw.getD 0 []) p)

end CFSG.KD.SuzDc2

#lc_blocks CFSG.KD.SuzDc2.W0B CFSG.KD.SuzDc2.w0 22880 2080

end
