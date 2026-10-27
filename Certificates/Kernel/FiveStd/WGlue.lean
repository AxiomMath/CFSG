module

public import Certificates.Kernel.FiveStd.CandGlue
public import Certificates.Kernel.FiveStd.WChk

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.Five

local instance instFact5'' : Fact (Nat.Prime 5) := fact5

local notation "ιF" => Mat.ιF (ZMod 5)

theorem prod2_codes (g2 : E) : (prod2 (powers g2 5) K1l).map codeE = p2K K1c (codeE g2) := by
  unfold prod2 mulLL p2K
  rw [List.map_flatMap, ← map_powers g2 5, List.flatMap_map]
  refine List.flatMap_congr fun x _ => ?_
  rw [List.map_map, ← K1l_codes, List.map_map]
  refine List.map_congr_left fun y _ => ?_
  exact codeE_mulE x y

theorem conj_oneE {x : E} (hx : validE x = true) : conjE oneE x = x := by
  apply hM5.inj _ _ (hM5.valid_conjE hM5.valid_one hx) hx
  rw [hM5.map_conjE hM5.valid_one hx, hM5.map_one]
  group

theorem cen_filter_of {t g : E} (ht : validE t = true) (hg : validE g = true) {g2c dc : Nat}
    (hcl : (Nat.beq (cjK (codeE t) (invK (codeE t)) (codeE g)) g2c &&
      Nat.beq (cjK dc (invK dc) (RP.getD 2 0)) g2c) = true)
    (hdc : validK dc = true)
    (hsub : cenSubK (p2K K1c g2c) (CB.getD 2 0) (CM.getD 2 0) dc (invK dc) = true)
    (hsup : cenSupK (p2K K1c g2c) g2c = true) :
    eqL (Cs.filter fun c => cenG c [conjE t g]) (prod2 (powers (conjE t g) 5) K1l) = true := by
  rw [Bool.and_eq_true, beq_iff_eq', beq_iff_eq'] at hcl
  obtain ⟨h1, h2⟩ := hcl
  set g2 := conjE t g with hg2d
  have hg2 : validE g2 = true := hM5.valid_conjE ht hg
  have hg2c : codeE g2 = g2c := by rw [hg2d, conj_code, h1]
  obtain ⟨hrk, -⟩ := cls_glue 2 (by norm_num)
  have hrc : codeE (decE (RP.getD 2 0)) = RP.getD 2 0 :=
    codeE_decE (validK_lt (clsOK_spec (clsF_eq 2 ▸ cls_ok 2 (by norm_num))).2.1)
  set d := decE dc
  have hd : validE d = true := valid_decE hdc
  have hdcode : codeE d = dc := codeE_decE (validK_lt hdc)
  have hgd : g2 = conjE d (decE (RP.getD 2 0)) := by
    apply codeE_injective
    rw [hg2c, conj_code, hdcode, hrc, h2]
  have hP := prod2_codes g2
  rw [hg2c] at hP
  unfold eqL subL
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  constructor
  · intro c hc
    obtain ⟨hcC, hcen⟩ := List.mem_filter.1 hc
    have hcv := (mem_Cs_iff c).1 hcC
    have hcomm : mulE c g2 = mulE g2 c := by
      unfold cenG at hcen
      rw [List.all_cons, List.all_nil, Bool.and_true, commE, beq_iff_eq] at hcen
      exact hcen
    have hcy : conjE c g2 = g2 := by
      apply hM5.inj _ _ (hM5.valid_conjE hcv hg2) hg2
      have := congrArg ιF hcomm
      rw [hM5.map_mul _ _ hcv hg2, hM5.map_mul _ _ hg2 hcv] at this
      rw [hM5.map_conjE hcv hg2, this]
      group
    obtain ⟨j, hj, hcj⟩ := conj_cands (by norm_num) hd hgd hM5.valid_one (conj_oneE hg2) hcv hcy
    rw [oneE_mulE (hM5.valid_conjE hd (valid_decE (cb_valid 2 (by norm_num) j hj)))] at hcj
    have hm := (allN_iff _ _).1 hsub j hj
    rw [memL_eq] at hm
    rw [inL_codeE, hP, hcj, conj_code, hdcode, codeE_decE (validK_lt (cb_valid 2 (by norm_num) j hj))]
    exact hm
  · intro y hy
    have hyc : codeE y ∈ p2K K1c g2c := by
      rw [← hP]
      exact List.mem_map_of_mem hy
    have hf := List.all_eq_true.1 (by rw [← allL_eq]; exact hsup) (codeE y) hyc
    rw [andB_eq, Bool.and_eq_true, validK_codeE, ← hg2c, ← commE_codeE] at hf
    unfold inL
    rw [List.contains_iff_mem, List.mem_filter]
    refine ⟨(mem_Cs_iff y).2 hf.1, ?_⟩
    unfold cenG
    rw [List.all_cons, List.all_nil, Bool.and_true]
    exact hf.2

end CertificateChecks.FiveStd

end
