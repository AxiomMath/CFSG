module

public import Certificates.Data.Kernel.L5.Eng0D
public import Certificates.Data.Kernel.L5.GrpOf
public import CFSG.Certificates.Kernel.Common.DecideFV

public section

namespace CFSG.KD.L5.E0

open CFSG.GH74.GLS.C3.Layer2.L5.Fus CFSG.KD CFSG.KD.L5

variable (G : Group (Idx 128)) (hm : ∀ a b, mul a b = G.mul a b) (hi : ∀ a, inv a = G.inv a)
  (ho : one = G.one)

theorem csz0 : @cszChk 128 (grpOf G mul hm inv hi one ho) eng.cszA = true := by
  kc_decide_fv

theorem mg0 : @mgChk 128 (grpOf G mul hm inv hi one ho) mgens eng.maxSubs = true := by
  kc_decide_fv

theorem ctxR0 : @ctxChk 128 (grpOf G mul hm inv hi one ho) eng.reps ctxs = true := by
  kc_decide_fv

end CFSG.KD.L5.E0

end
