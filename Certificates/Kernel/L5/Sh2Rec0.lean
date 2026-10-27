module

public import Certificates.Data.Kernel.L5.EngRec
public import Certificates.Data.Kernel.L5.Sh2EngD
public import Certificates.Data.Kernel.L5.GrpOf
public import CFSG.Certificates.Kernel.Common.DecideFV

public section

namespace CFSG.KD.L5.Sh2Rec

open CFSG.GH74.GLS.C3.Layer2.L5.Fus CFSG.KD CFSG.KD.L5

variable (G : Group (Idx 256)) (hm : ∀ a b, mulI 0 a b = G.mul a b)
  (hi : ∀ a, invI 0 a = G.inv a) (ho : oneI = G.one)

theorem csz0 : @cszChk 256 (grpOf G (mulI 0) hm (invI 0) hi oneI ho) (engA 0).cszA = true := by
  kc_decide_fv

theorem mg0 : @mgChk 256 (grpOf G (mulI 0) hm (invI 0) hi oneI ho) mgensR (engA 0).maxSubs =
    true := by
  kc_decide_fv

theorem ctxR0 : @ctxChk 256 (grpOf G (mulI 0) hm (invI 0) hi oneI ho) (engA 0).reps ctxA =
    true := by
  kc_decide_fv

end CFSG.KD.L5.Sh2Rec

end
