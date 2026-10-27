module

public import Certificates.Data.Kernel.L5.Sh2EngD
public import Certificates.Data.Kernel.L5.GrpOf
public import CFSG.Certificates.Kernel.Common.DecideFV

public section

namespace CFSG.KD.L5.Sh2Eng

open CFSG.GH74.GLS.C3.Layer2.L5.Fus CFSG.KD CFSG.KD.L5

variable (G : Group (Idx 256)) (hm : ∀ a b, mulI 1 a b = G.mul a b)
  (hi : ∀ a, invI 1 a = G.inv a) (ho : oneI = G.one)

theorem mgens1 :
    @genChk 256 (grpOf G (mulI 1) hm (invI 1) hi oneI ho) (elemsI 256) [] mgensR = true := by
  kc_decide_fv

theorem ctx1 :
    @ctxGensChk 256 (grpOf G (mulI 1) hm (invI 1) hi oneI ho) (engB 1).reps ctxB = true := by
  kc_decide_fv

theorem wit1 : @allWit 256 (grpOf G (mulI 1) hm (invI 1) hi oneI ho) (engB 1) tagsB = true := by
  kc_decide_fv

end CFSG.KD.L5.Sh2Eng

end
