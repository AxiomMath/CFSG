module

public import Certificates.Data.Kernel.L5.Eng0D
public import Certificates.Data.Kernel.L5.GrpOf
public import CFSG.Certificates.Kernel.Common.DecideFV

public section

namespace CFSG.KD.L5.E0

open CFSG.GH74.GLS.C3.Layer2.L5.Fus CFSG.KD CFSG.KD.L5

variable (G : Group (Idx 128)) (hm : ∀ a b, mul a b = G.mul a b) (hi : ∀ a, inv a = G.inv a)
  (ho : one = G.one)

theorem surv0 : @survChk 128 (grpOf G mul hm inv hi one ho) eng ctxs ld0 paths = true := by
  kc_decide_fv

end CFSG.KD.L5.E0

end
