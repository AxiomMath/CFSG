module

public import Certificates.Data.Kernel.L5.Sh2EngD
public import Certificates.Data.Kernel.L5.GrpOf
public import CFSG.Certificates.Kernel.Common.DecideFV
public import Certificates.Kernel.L5.WitSplit

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

theorem wit2n : decide (tagsA.length = (leaders (engA 2).reps.length).length) = true := by
  kc_decide_fv

theorem wit2p0 : (((leaders (engA 2).reps.length).zip tagsA).take 51).all
    (fun p => @witOK 256 (grpOf G (mulI 2) hm (invI 2) hi oneI ho) (engA 2) p.1 p.2) = true := by
  kc_decide_fv

theorem wit2p1 : ((((leaders (engA 2).reps.length).zip tagsA).drop 51).take 51).all
    (fun p => @witOK 256 (grpOf G (mulI 2) hm (invI 2) hi oneI ho) (engA 2) p.1 p.2) = true := by
  kc_decide_fv

theorem wit2p2 : (((((leaders (engA 2).reps.length).zip tagsA).drop 51).drop 51).take 51).all
    (fun p => @witOK 256 (grpOf G (mulI 2) hm (invI 2) hi oneI ho) (engA 2) p.1 p.2) = true := by
  kc_decide_fv

theorem wit2p3 : (((((leaders (engA 2).reps.length).zip tagsA).drop 51).drop 51).drop 51).all
    (fun p => @witOK 256 (grpOf G (mulI 2) hm (invI 2) hi oneI ho) (engA 2) p.1 p.2) = true := by
  kc_decide_fv

theorem wit2 : @allWit 256 (grpOf G (mulI 2) hm (invI 2) hi oneI ho) (engA 2) tagsA = true :=
  @allWit_of_parts 256 (grpOf G (mulI 2) hm (invI 2) hi oneI ho) (engA 2) tagsA 51 wit2n
    (wit2p0 G hm hi ho) (wit2p1 G hm hi ho) (wit2p2 G hm hi ho) (wit2p3 G hm hi ho)

end CFSG.KD.L5.Sh2Eng

end
