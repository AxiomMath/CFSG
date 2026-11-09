module

public import Certificates.Data.Kernel.L5.Sh2EngD
public import Certificates.Data.Kernel.L5.GrpOf
public import CFSG.Certificates.Kernel.Common.DecideFV
public import Certificates.Kernel.L5.WitSplit

public section

namespace CFSG.KD.L5.Sh2Eng

open CFSG.GH74.GLS.C3.Layer2.L5.Fus CFSG.KD CFSG.KD.L5

variable (G : Group (Idx 256)) (hm : ∀ a b, mulI 0 a b = G.mul a b)
  (hi : ∀ a, invI 0 a = G.inv a) (ho : oneI = G.one)

theorem mgens0 :
    @genChk 256 (grpOf G (mulI 0) hm (invI 0) hi oneI ho) (elemsI 256) [] mgensR = true := by
  kc_decide_fv

theorem ctx0 :
    @ctxGensChk 256 (grpOf G (mulI 0) hm (invI 0) hi oneI ho) (engA 0).reps ctxA = true := by
  kc_decide_fv

theorem wit0n : decide (tagsA.length = (leaders (engA 0).reps.length).length) = true := by
  kc_decide_fv

theorem wit0p0 : (((leaders (engA 0).reps.length).zip tagsA).take 51).all
    (fun p => @witOK 256 (grpOf G (mulI 0) hm (invI 0) hi oneI ho) (engA 0) p.1 p.2) = true := by
  kc_decide_fv

theorem wit0p1 : ((((leaders (engA 0).reps.length).zip tagsA).drop 51).take 51).all
    (fun p => @witOK 256 (grpOf G (mulI 0) hm (invI 0) hi oneI ho) (engA 0) p.1 p.2) = true := by
  kc_decide_fv

theorem wit0p2 : (((((leaders (engA 0).reps.length).zip tagsA).drop 51).drop 51).take 51).all
    (fun p => @witOK 256 (grpOf G (mulI 0) hm (invI 0) hi oneI ho) (engA 0) p.1 p.2) = true := by
  kc_decide_fv

theorem wit0p3 : (((((leaders (engA 0).reps.length).zip tagsA).drop 51).drop 51).drop 51).all
    (fun p => @witOK 256 (grpOf G (mulI 0) hm (invI 0) hi oneI ho) (engA 0) p.1 p.2) = true := by
  kc_decide_fv

theorem wit0 : @allWit 256 (grpOf G (mulI 0) hm (invI 0) hi oneI ho) (engA 0) tagsA = true :=
  @allWit_of_parts 256 (grpOf G (mulI 0) hm (invI 0) hi oneI ho) (engA 0) tagsA 51 wit0n
    (wit0p0 G hm hi ho) (wit0p1 G hm hi ho) (wit0p2 G hm hi ho) (wit0p3 G hm hi ho)

end CFSG.KD.L5.Sh2Eng

end
