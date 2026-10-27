module

public import Certificates.Kernel.L34W.ChCover
public import Certificates.Kernel.L34W.Glue
public import CFSG.Certificates.Kernel.L34W.ChCoverSound
import Certificates.Kernel.Sporadic.OddCore.PEnumGlue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelL34W

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.L34W
open CFSG.PSL3Four.Native CFSG.OddStandard.ChengHeldData
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real

theorem kap0 : kapOf 0 = ((1 : ZMod 4), (2 : ZMod 4)) := rfl
theorem kap1 : kapOf 1 = ((1 : ZMod 4), (0 : ZMod 4)) := rfl

theorem frame4_true : frame4OK = true := by
  have h := ch6136_f4
  simp only [bAnd_and, Bool.and_eq_true] at h
  unfold frame4OK
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [frM_eq (by norm_num : 0 < 3), frM_eq (by norm_num : 1 < 3), kap0, kap1,
    relsOK_eq t1Of bounds_k (frC_lt 0) eqKM12_dec, relsOK_eq t1Of bounds_k (frC_lt 1) eqKM10_dec]
  simp only [h.1, h.2, Bool.and_self]

theorem act4_true : act4OK = true := by
  have h := ch6136_a4
  simp only [bAnd_and, Bool.and_eq_true] at h
  unfold act4OK
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [frM_eq (by norm_num : 0 < 3), frM_eq (by norm_num : 1 < 3), kap0, kap1,
    actOK_eq t1Of alOf bounds_k (frC_lt 0) eqKM12_dec (i := 1) (by norm_num),
    actOK_eq t1Of alOf bounds_k (frC_lt 0) eqKM12_dec (i := 2) (by norm_num),
    actOK_eq t1Of alOf bounds_k (frC_lt 0) eqKM12_dec (i := 3) (by norm_num),
    actOK_eq t1Of alOf bounds_k (frC_lt 1) eqKM10_dec (i := 1) (by norm_num),
    actOK_eq t1Of alOf bounds_k (frC_lt 1) eqKM10_dec (i := 2) (by norm_num),
    actOK_eq t1Of alOf bounds_k (frC_lt 1) eqKM10_dec (i := 3) (by norm_num)]
  simp only [h, Bool.and_self]

theorem frame2_true : frame2OK = true := by
  unfold frame2OK
  rw [frM_eq (by norm_num : 2 < 3), relsOK_eq t1Of bounds_k (frC_lt 2) eqN2_dec]
  exact ch6136_f2

theorem act2_true : act2OK = true := by
  have h := ch6136_a2
  simp only [bAnd_and, Bool.and_eq_true] at h
  unfold act2OK
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [frM_eq (by norm_num : 2 < 3),
    actOK_eq t1Of alOf bounds_k (frC_lt 2) eqN2_dec (i := 1) (by norm_num),
    actOK_eq t1Of alOf bounds_k (frC_lt 2) eqN2_dec (i := 2) (by norm_num),
    actOK_eq t1Of alOf bounds_k (frC_lt 2) eqN2_dec (i := 3) (by norm_num)]
  simp only [h, Bool.and_self]

theorem al64 {i : ℕ} (hi : i < 36) : alphaEntry i 64 = quad (ent AlX.F i 64) :=
  alOf i 64 hi (by norm_num)

theorem al65 {i : ℕ} (hi : i < 36) : alphaEntry i 65 = quad (ent AlX.F i 65) :=
  alOf i 65 hi (by norm_num)

theorem gTrivial_true : gTrivialOK = true := by
  unfold gTrivialOK mact
  simp only [al64 (show 31 < 36 by norm_num), al65 (show 31 < 36 by norm_num)]
  decide +kernel

theorem gAct_true : gActOK = true := by
  have h := ch6136_g
  simp only [bAnd_and, Bool.and_eq_true] at h
  unfold gActOK
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [frM_eq (by norm_num : 0 < 3), frM_eq (by norm_num : 1 < 3), frM_eq (by norm_num : 2 < 3),
    kap0, kap1,
    actOK_eq t1Of alOf bounds_k (frC_lt 0) eqKM12_dec (i := 31) (by norm_num),
    actOK_eq t1Of alOf bounds_k (frC_lt 1) eqKM10_dec (i := 31) (by norm_num),
    actOK_eq t1Of alOf bounds_k (frC_lt 2) eqN2_dec (i := 31) (by norm_num), gTrivial_true]
  simp only [h, Bool.and_self]

theorem twist_true : twistOK = true := by
  unfold twistOK
  simp only [List.any_cons, List.any_nil, Bool.or_false, mact,
    al64 (show 0 < 36 by norm_num), al65 (show 0 < 36 by norm_num),
    al64 (show 4 < 36 by norm_num), al65 (show 4 < 36 by norm_num),
    al64 (show 5 < 36 by norm_num), al65 (show 5 < 36 by norm_num)]
  decide +kernel

theorem kappaFG_true : kappaFGOK = true := by
  unfold kappaFGOK liftsK
  simp only [al64 (show 1 < 36 by norm_num), al65 (show 1 < 36 by norm_num),
    al64 (show 2 < 36 by norm_num), al65 (show 2 < 36 by norm_num)]
  decide +kernel

theorem twist2_true : twist2OK = true := by
  unfold twist2OK
  simp only [List.any_cons, List.any_nil, Bool.or_false, mact,
    al64 (show 0 < 36 by norm_num), al65 (show 0 < 36 by norm_num),
    al64 (show 4 < 36 by norm_num), al65 (show 4 < 36 by norm_num),
    al64 (show 5 < 36 by norm_num), al65 (show 5 < 36 by norm_num)]
  decide +kernel

theorem kappa2FG_true : kappa2FGOK = true := by
  unfold kappa2FGOK lifts2 mact
  simp only [al64 (show 1 < 36 by norm_num), al65 (show 1 < 36 by norm_num),
    al64 (show 2 < 36 by norm_num), al65 (show 2 < 36 by norm_num)]
  decide +kernel

theorem gen_of {j t : ℕ} (h : Nat.beq (CC.G j) (tgK GT t) = true) :
    wordTab (tg t) = unpack 42 6 (CC.G j) ∧ canonK 42 6 (mask 6) (42 * 6) (CC.G j) = true := by
  rw [Nat.eq_of_beq_eq_true h]
  exact ⟨(tgK_eq gensG t).2, (tgK_eq gensG t).1⟩

theorem wordTabs_frTg : wordTabs frTg = #[wordTab (tg 4), wordTab (tg 8), wordTab (tg 3),
    wordTab (tg 2), wordTab (tg 24), wordTab (tg 16)] := rfl

theorem gensCC : GensOK 42 6 6 CC.G (wordTabs frTg) := by
  have h := ch6136_gens
  simp only [bAnd_and, Bool.and_eq_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  rw [wordTabs_frTg]
  refine ⟨rfl, fun j hj => ?_⟩
  interval_cases j
  · exact gen_of h0
  · exact gen_of h1
  · exact gen_of h2
  · exact gen_of h3
  · exact gen_of h4
  · exact gen_of h5

theorem genT0_true : genT0OK = true := by
  have hp : ∀ i < 64, penumPtK 42 6 (mask 6) (42 * 6) false CC.G CC.GI 6 64 CC.T CC.PL
      CC.POS CC.SRT CC.SRI i = true := fun i hi =>
    penumSl_spec ch6136_sl i (Nat.zero_le _) (by omega) hi
  have henum := penumK_left_sound (cap := 64) szOK42 gensCC ch6136_hd hp
  unfold genT0OK
  rw [henum.1, henum.2, penumRec_eq, Array.size_ofFn]
  rfl

theorem comm_true : CFSG.OddStandard.ChengHeldData.commOK = true := by
  have h := ch6136_comm
  simp only [bAnd_and, Bool.and_eq_true] at h
  have r3 := repK_eq gensG (i := 3) (by norm_num)
  have r4 := repK_eq gensG (i := 4) (by norm_num)
  have r5 := repK_eq gensG (i := 5) (by norm_num)
  unfold CFSG.OddStandard.ChengHeldData.commOK
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [r3.2, r4.2, r5.2, CFSG.KC.L34KSnd.comp_unpack' r4.1 r3.1,
    CFSG.KC.L34KSnd.comp_unpack' r3.1 r4.1, CFSG.KC.L34KSnd.comp_unpack' r5.1 r3.1,
    CFSG.KC.L34KSnd.comp_unpack' r3.1 r5.1, Nat.eq_of_beq_eq_true h.1,
    Nat.eq_of_beq_eq_true h.2]
  simp

theorem chCover_true : chCoverOK = true := by
  unfold chCoverOK
  rw [frame4_true, act4_true, frame2_true, act2_true, genT0_true, twist_true, kappaFG_true,
    twist2_true, kappa2FG_true, comm_true, gAct_true]
  rfl

end CertificateChecks.KernelL34W

end
