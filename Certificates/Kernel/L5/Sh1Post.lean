module

public import Certificates.Data.Kernel.L5.Sh1EngD
public import Certificates.Data.Kernel.L5.GrpOf
public import CFSG.Certificates.Kernel.Common.DecideFV

public section

namespace CFSG.KD.L5.Sh1

open CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.Fus CFSG.KD CFSG.KD.L5

variable
  (G : Group (Idx 128)) (hm : ∀ a b, mul1 a b = G.mul a b)
  (hi : ∀ a, inv1 a = G.inv a) (ho : one1 = G.one)

theorem post1 : ((List.finRange 16).any fun a => (List.finRange 16).any fun b =>
    @isInv 128 (grpOf G mul1 hm inv1 hi one1 ho) (embL1 (elT a)) &&
      @isInv 128 (grpOf G mul1 hm inv1 hi one1 ho) (embL1 (elT b)) &&
      decide (blkOf eng1R.ciA ld1 (embL1 (elT a)) = blkOf eng1R.ciA ld1 (embL1 (elT b))) &&
      !(n24L.any fun A => decide (A a = b))) = true := by
  kc_decide_fv

end CFSG.KD.L5.Sh1

end
