module

public import Certificates.Data.Kernel.L5.EngRec
public import Certificates.Data.Kernel.L5.Sh1EngD
public import Certificates.Data.Kernel.L5.GrpOf
public import CFSG.Certificates.Kernel.Common.DecideFV

public section

namespace CFSG.KD.L5.Sh1

open CFSG.GH74.GLS.C3.Layer2.L5.Fus CFSG.KD CFSG.KD.L5

variable (G : Group (Idx 128)) (hm : ∀ a b, mul1 a b = G.mul a b)
  (hi : ∀ a, inv1 a = G.inv a) (ho : one1 = G.one)

theorem csz1 : @cszChk 128 (grpOf G mul1 hm inv1 hi one1 ho) eng1R.cszA = true := by
  kc_decide_fv

theorem mg1 : @mgChk 128 (grpOf G mul1 hm inv1 hi one1 ho) mgens1 eng1R.maxSubs = true := by
  kc_decide_fv

theorem ctxR1 : @ctxChk 128 (grpOf G mul1 hm inv1 hi one1 ho) eng1R.reps ctx1 = true := by
  kc_decide_fv

end CFSG.KD.L5.Sh1

end
