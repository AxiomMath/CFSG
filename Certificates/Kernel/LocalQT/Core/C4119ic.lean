module

public import Certificates.Data.Kernel.LocalQT.M24L
public import Certificates.Kernel.LocalQT.Core.D4119hexE
public import Certificates.Kernel.LocalQT.Core.D4119w
public import Certificates.Kernel.LocalQT.Core.D4119i3

public section

namespace CFSG.KD.LQT.C4119i

open CFSG.KC.LQT.S CFSG.KC.LQT.W CFSG.KC.LQT.M24 CFSG.KD.LQT.C4119w

@[expose] noncomputable def iC (j : Nat) : Bool :=
  isetChunk 24 (getK C4119hexE.GL 0) (getK C4119hexE.GL 1) (getK C4119hexE.GL 2)
    (getK C4119hexE.GL 3) S 30 (evalWK 24 C4119hexE.GL xWL)
    [El_hexE, El_octE1, El_octE2, El_octE3, El_octE4] IL (ILs.getD j []) (Hs.getD j [])

end CFSG.KD.LQT.C4119i

end
