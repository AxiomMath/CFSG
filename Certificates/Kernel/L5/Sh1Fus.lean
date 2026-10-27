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

theorem fus1 : @fusChkL 128 (grpOf G mul1 hm inv1 hi one1 ho)
    (@fuseL 128 (grpOf G mul1 hm inv1 hi one1 ho)
      (f5P eI1 (Sh2FusT.embT.map Prod.fst) Sh2FusT.f5C) (nbarPairsF embL1))
    (embL1 x0T5) eng1R.reps eng1R.ciA eng1R.invs eng1R.x = true := by
  kc_decide_fv

end CFSG.KD.L5.Sh1

end
