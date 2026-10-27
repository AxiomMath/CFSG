module

public import Certificates.Kernel.FiveStd.WGlue5
public import Certificates.Kernel.FiveStd.NoInvGlue
public import Certificates.Kernel.FiveStd.BaseGlue
public import Certificates.Kernel.FiveStd.SylGlue
public import Certificates.Kernel.FiveStd.DiagCheck
public import Certificates.Kernel.FiveStd.CoverGlue
public import Certificates.Kernel.FiveStd.WChk5

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.Five

theorem head_codes (u : E) (j : Nat) (hj : j < 3) (hu : codeE u = PU.getD j 0) :
    ∃ a b, (tpOf u).head? = some (a, b) ∧ codeE a = (TPc j).1 ∧ codeE b = (TPc j).2 := by
  have hu' : u = decE (PU.getD j 0) := by rw [← hu, decE_codeE]
  subst hu'
  have hh := congrArg List.head? (tpOf_codes j hj)
  rw [List.head?_map, pl_head j hj, Option.map_eq_some_iff] at hh
  obtain ⟨⟨a, b⟩, hab, he⟩ := hh
  exact ⟨a, b, hab, by rw [← he], by rw [← he]⟩

theorem ht1 : HT 1 = HT 0 := rfl

theorem checkRep_gen {t u : E} {j : Nat} (hj : j < 3) (hu : codeE u = PU.getD j 0)
    (hP : checkPK K1c (codeE t) (codeE u) (TPc j).1 (TPc j).2 (PLc j) (tpL (E4c j)) = true)
    (hW : ∀ a b : E, codeE a = (TPc j).1 → codeE b = (TPc j).2 → checkW t u a b = true) :
    checkRep t u = true := by
  obtain ⟨a, b, hab, e1, e2⟩ := head_codes u j hj hu
  have hH : (ppE a b 4 4).map codeE = HT j := by rw [map_ppE, e1, e2, ht_eq j hj]
  have hN : noInvCheck (ppE a b 4 4) = true := by
    have hj3 : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj3 with rfl | rfl | rfl
    · exact noInv_tori _ 0 (Or.inl rfl) hH
    · exact noInv_tori _ 0 (Or.inl rfl) (hH.trans ht1)
    · exact noInv_tori _ 2 (Or.inr rfl) hH
  have hu' : u = decE (PU.getD j 0) := by rw [← hu, decE_codeE]
  have hS : sylowTorusCheck (PlOf u) = true := by
    rw [hu']
    exact sylowTorus_reps j hj
  have hPc : checkP t u a b = true := by
    rw [checkP_code, e1, e2, hu', PlOf_codes j hj, tpOf_codes j hj, ← hu']
    exact hP
  unfold checkRep
  rw [hab]
  dsimp only
  unfold checkN
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨hPc, hW a b e1 e2⟩, hN, hS⟩

theorem g82001 : ∃ g ∈ X1cands, codeE g = 82001 := mem_codes X1cands_codes (by decide)

theorem g29501 : ∃ g ∈ X1cands, codeE g = 29501 := mem_codes X1cands_codes (by decide)

theorem rep0 {t u : E} (ht : codeE t = 409405) (hu : codeE u = 81126) : checkRep t u = true := by
  have hP := pl_checkP 0 (by norm_num)
  obtain ⟨g, hgX, hg⟩ := g82001
  refine checkRep_gen (j := 0) (by norm_num) (hu.trans rk_pu.1) (by rw [ht, hu]; exact hP) fun a b ha hb => ?_
  refine checkW_of hgX (good0 ht hg ha hb ?_) ?_
  · rw [ht, hu, ha, hb, hg]
    exact wr_rest 0 (by norm_num)
  · rw [ht, hu, ha, hb, hg]
    exact ww0

theorem rep1 {t u : E} (ht : codeE t = 409405) (hu : codeE u = 80754) : checkRep t u = true := by
  have hP := pl_checkP 1 (by norm_num)
  obtain ⟨g, hgX, hg⟩ := g82001
  refine checkRep_gen (j := 1) (by norm_num) (hu.trans rk_pu.2.1) (by rw [ht, hu]; exact hP) fun a b ha hb => ?_
  refine checkW_of hgX (good0 ht hg ha hb ?_) ?_
  · rw [ht, hu, ha, hb, hg]
    exact wr_rest 1 (by norm_num)
  · rw [ht, hu, ha, hb, hg]
    exact ww1

theorem rep2 {t u : E} (ht : codeE t = 415680) (hu : codeE u = 81126) : checkRep t u = true := by
  have hP := pl_checkP 2 (by norm_num)
  obtain ⟨g, hgX, hg⟩ := g82001
  refine checkRep_gen (j := 0) (by norm_num) (hu.trans rk_pu.2.2.1) (by rw [ht, hu]; exact hP)
    fun a b ha hb => ?_
  refine checkW_of hgX (good1 ht hg ha hb ?_) ?_
  · rw [ht, hu, ha, hb, hg]
    exact wr_rest 2 (by norm_num)
  · rw [ht, hu, ha, hb, hg]
    exact ww2

theorem rep3 {t u : E} (ht : codeE t = 415680) (hu : codeE u = 18835) : checkRep t u = true := by
  have hP := pl_checkP 3 (by norm_num)
  obtain ⟨g, hgX, hg⟩ := g29501
  refine checkRep_gen (j := 2) (by norm_num) (hu.trans rk_pu.2.2.2) (by rw [ht, hu]; exact hP)
    fun a b ha hb => ?_
  refine checkW_of hgX (good2 ht hg ha hb ?_) ?_
  · rw [ht, hu, ha, hb, hg]
    exact wr_rest 3 (by norm_num)
  · rw [ht, hu, ha, hb, hg]
    exact ww3

theorem checkRep_reps : (reps.all fun r => checkRep r.1 r.2) = true := by
  rw [List.all_eq_true]
  intro r hr
  obtain ⟨k, hk, hrk⟩ := reps_index r hr
  have h1 : codeE r.1 = (RK.getD k (0, 0)).1 := by rw [hrk]
  have h2 : codeE r.2 = (RK.getD k (0, 0)).2 := by rw [hrk]
  interval_cases k
  · exact rep0 h1 h2
  · exact rep1 h1 h2
  · exact rep2 h1 h2
  · exact rep3 h1 h2

theorem five_std_check : fiveStdCheck = true := by
  unfold fiveStdCheck
  rw [base_check, syl_cover, diag_check, cover_check, checkRep_reps]
  rfl

end CertificateChecks.FiveStd

end
