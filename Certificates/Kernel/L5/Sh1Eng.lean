module

public import Certificates.Data.Kernel.L5.Sh1EngD
public import Certificates.Data.Kernel.L5.GrpOf
public import CFSG.Certificates.Kernel.Common.DecideFV

public section

namespace CFSG.KD.L5.Sh1

open CFSG.GH74.GLS.C3.Layer2.L5.Fus CFSG.KD CFSG.KD.L5

variable (G : Group (Idx 128)) (hm : ∀ a b, mul1 a b = G.mul a b)
  (hi : ∀ a, inv1 a = G.inv a) (ho : one1 = G.one)

theorem mgens1_chk :
    @genChk 128 (grpOf G mul1 hm inv1 hi one1 ho) (elemsI 128) [] mgens1 = true := by
  kc_decide_fv

theorem ctx1_chk : @ctxGensChk 128 (grpOf G mul1 hm inv1 hi one1 ho) eng1R.reps ctx1 = true := by
  kc_decide_fv

theorem surv1 : @survChk 128 (grpOf G mul1 hm inv1 hi one1 ho) eng1R ctx1 ld1 paths1 = true := by
  kc_decide_fv

theorem wit1 : @allWit1 128 (grpOf G mul1 hm inv1 hi one1 ho) eng1R ctx1 ld1 Sh1R.tags = true := by
  kc_decide_fv

end CFSG.KD.L5.Sh1

end
