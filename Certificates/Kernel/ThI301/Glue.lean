module

public import CFSG.Certificates.Kernel.ThI301.Sound
public import Certificates.Kernel.ThI301.Checks
public import CFSG.Sporadic.ThI301.Inputs

public section

namespace CertificateChecks.ThI301K

open CFSG.KC.Enum CFSG.KC.ThI301 CFSG.KC.EnumSound CFSG.KC.ThI301Sound CFSG.KD.ThI301 CFSG.KS
  CFSG.KS.Raw.Orb CFSG.Sporadic.ThI301 Equiv

theorem pm_val : PM = 68719476735 := Nat.eq_of_beq_eq_true pm_eq

theorem gen_prep : PRep 9 4 A (swap 0 1) ∧ PRep 9 4 AI (swap 0 1)⁻¹ ∧
    PRep 9 4 B (finRotate 9) ∧ PRep 9 4 BI (finRotate 9)⁻¹ := by
  unfold PRep
  decide +kernel

theorem y_prep :
    ∀ k < 3, PRep 9 4 (yP k) (a9Conj.getD k 1) ∧ PRep 9 4 (yPI k) (a9Conj.getD k 1)⁻¹ := by
  unfold PRep
  decide +kernel

theorem rep_prep : PRep 9 4 (rperm IT 0 0 0 RO PM 0) rep1 ∧ PRep 9 4 (rperm IT 0 0 0 RO PM 1) rep2 ∧
    PRep 9 4 (rperm IT 0 0 0 RO PM 2) rep3 ∧ PRep 9 4 (rperm IT 0 0 0 RO PM 3) rep4 := by
  unfold PRep
  decide +kernel

theorem lChk_all : ∀ i < NL, lChk IT 0 0 0 RO 9 4 (mask 4) 36 PM 12 4095 NL A AI B BI i = true := by
  intro i hi
  rw [Nat.eq_of_beq_eq_true nL_eq] at hi
  have h := lRange_iff.1 l_all i hi
  have hm : mask 4 = 15 := rfl
  rw [Nat.zero_add] at h
  rw [hm]
  exact h

theorem th_check : ∀ X : Perm (Fin 9), X * X = 1 → X ≠ 1 →
    ∃ Y ∈ a9Conj, X * (Y * X * Y⁻¹) ≠ Y * X * Y⁻¹ * X := by
  intro X h2 h1
  obtain ⟨ha, hai, hb, hbi⟩ := gen_prep
  obtain ⟨U, hU, hUc⟩ := lList_prep lChk_all ha hai hb hbi
  have hnL : NL = 2619 := Nat.eq_of_beq_eq_true nL_eq
  have hrep : ∀ r ∈ [rep1, rep2, rep3, rep4], ∃ j < NL, U j = r := by
    obtain ⟨r1, r2, r3, r4⟩ := rep_prep
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨0, by omega, prep_unique (hU 0 (by omega)).1 r1⟩
    · exact ⟨1, by omega, prep_unique (hU 1 (by omega)).1 r2⟩
    · exact ⟨2, by omega, prep_unique (hU 2 (by omega)).1 r3⟩
    · exact ⟨3, by omega, prep_unique (hU 3 (by omega)).1 r4⟩
  obtain ⟨r, hr, hc⟩ : ∃ r ∈ [rep1, rep2, rep3, rep4], IsConj X r := by
    rcases invol_isConj_rep h2 h1 with h | h | h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
  obtain ⟨j, hj, hUj⟩ := hrep r hr
  obtain ⟨c, hcr⟩ := isConj_iff.1 hc
  have hcl : c⁻¹ ∈ Subgroup.closure ({swap 0 1, finRotate 9} : Set (Perm (Fin 9))) := by
    rw [closure_swap_finRotate]
    exact Subgroup.mem_top _
  obtain ⟨i, hi, hUi⟩ := mem_of_conj_closed (fun i hi => (hUc i hi).1) (fun i hi => (hUc i hi).2)
    hcl hj
  have hXi : U i = X := by
    rw [hUi, hUj, ← hcr]
    group
  have hX : PRep 9 4 (Nat.land (rget IT 0 0 0 RO i) 68719476735) X := by
    have h := (hU i hi).1
    rw [hXi] at h
    unfold rperm at h
    rwa [pm_val] at h
  rw [hnL] at hi
  have hth := thRange_iff.1 th_all i hi
  rw [Nat.zero_add] at hth
  obtain ⟨k, hk, hne⟩ := thRec_prep hth hX y_prep
  refine ⟨a9Conj.getD k 1, ?_, hne⟩
  interval_cases k <;> simp [a9Conj]

end CertificateChecks.ThI301K

end
