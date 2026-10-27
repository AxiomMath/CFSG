module

public import Certificates.Data.Kernel.L5.EngRec
public import Certificates.Data.Kernel.L5.Sh2EngD
public import Certificates.Data.Kernel.L5.GrpOf
public import CFSG.Certificates.Kernel.Common.DecideFV

public section

namespace CFSG.KD.L5.Sh2Rec

open CFSG.GH74.GLS.C3.Layer2.L5.Fus CFSG.KD CFSG.KD.L5

variable (G : Group (Idx 256)) (hm : ∀ a b, mulI 3 a b = G.mul a b)
  (hi : ∀ a, invI 3 a = G.inv a) (ho : oneI = G.one)

theorem csz3 : @cszChk 256 (grpOf G (mulI 3) hm (invI 3) hi oneI ho) (engB 3).cszA = true := by
  kc_decide_fv

theorem mg3 : @mgChk 256 (grpOf G (mulI 3) hm (invI 3) hi oneI ho) mgensR (engB 3).maxSubs =
    true := by
  kc_decide_fv

theorem ctxR3 : @ctxChk 256 (grpOf G (mulI 3) hm (invI 3) hi oneI ho) (engB 3).reps ctxB =
    true := by
  kc_decide_fv

end CFSG.KD.L5.Sh2Rec

end
