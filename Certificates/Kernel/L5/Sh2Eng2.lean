module

public import Certificates.Data.Kernel.L5.Sh2EngD
public import Certificates.Data.Kernel.L5.GrpOf
public import CFSG.Certificates.Kernel.Common.DecideFV

public section

namespace CFSG.KD.L5.Sh2Eng

open CFSG.GH74.GLS.C3.Layer2.L5.Fus CFSG.KD CFSG.KD.L5

variable (G : Group (Idx 256)) (hm : ∀ a b, mulI 2 a b = G.mul a b)
  (hi : ∀ a, invI 2 a = G.inv a) (ho : oneI = G.one)

theorem mgens2 :
    @genChk 256 (grpOf G (mulI 2) hm (invI 2) hi oneI ho) (elemsI 256) [] mgensR = true := by
  kc_decide_fv

theorem ctx2 :
    @ctxGensChk 256 (grpOf G (mulI 2) hm (invI 2) hi oneI ho) (engA 2).reps ctxA = true := by
  kc_decide_fv

theorem wit2 : @allWit 256 (grpOf G (mulI 2) hm (invI 2) hi oneI ho) (engA 2) tagsA = true := by
  kc_decide_fv

end CFSG.KD.L5.Sh2Eng

end
