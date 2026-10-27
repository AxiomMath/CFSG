module

public import Certificates.Kernel.IdxFour.SiftOK
public import Certificates.Kernel.IdxFour.M0Coset
public import CFSG.Certificates.Kernel.IdxFourSiftSound
public import CFSG.GF2Type.Smith1979.IdxFourModelBasic

set_option maxRecDepth 100000

public section

namespace CFSG.KD.IF4R

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.IdxFour

local notation "GL" => V12 ≃ₗ[ZMod 2] V12

theorem rowsP_packR : ∀ r ∈ pGens ++ E0Chk.sGensE0 ++ sGens ++ lbarGens ++ skGens ++
    [s12Rows, omegaRows], rowsP (packR r) = r := by
  decide +kernel

theorem genGrp_le {gs : List (Array ℕ)} {K : Subgroup GL} (hr : ∀ r ∈ gs, rowsP (packR r) = r)
    (h : ∀ r ∈ gs, ∃ U ∈ K, IsP U (packR r)) : Viol.genGrp gs ≤ K := by
  rw [Viol.genGrp, Subgroup.closure_le]
  rintro l ⟨r, hr', hl⟩
  obtain ⟨U, hU, hUP⟩ := h r hr'
  have hUl : U = l := LinearEquiv.ext fun v =>
    ((isP_iff_of_rowsP (hr r hr') U).1 hUP v).trans (hl v).symm
  rw [← hUl]
  exact hU

theorem exists_rec {n : Nat} {f : Nat → Nat} {rs : List Nat} {ps : List (List Nat)}
    (h : recsOK CFSG.KD.IF4E.T CFSG.KD.IF4E.O n f rs ps = true) {r : Nat} (hr : r ∈ rs) :
    ∃ x < n, ∃ P ∈ E0, ∀ F : GL, IsP F (f x) → IsP (P * F) r := by
  obtain ⟨x, hx, as, hp, heq⟩ := recsOK_spec h r hr
  obtain ⟨P, hP, hPP⟩ := CFSG.KD.IF4M.exists_path hp
  exact ⟨x, hx, P, hP, fun F hF => heq ▸ hPP.mul hF⟩

theorem isP_s12e : IsP s12e (packR s12Rows) :=
  (isP_iff_of_rowsP (rowsP_packR _ (by simp)) _).2 fun _ => rfl

theorem isP_omegaE : IsP omegaE (packR omegaRows) :=
  (isP_iff_of_rowsP (rowsP_packR _ (by simp)) _).2 fun _ => rfl

theorem s12e_not_mem_E0 : s12e ∉ E0 := by
  intro h
  obtain ⟨hfix, hmove⟩ := cf17605aux
  simp only [List.all_eq_true, Nat.beq_eq] at hfix
  have h1 := CFSG.KD.IF4E.eq_one_of_fix_base h fun b hb => by
    rw [isP_s12e.apply_code, hfix b hb]
  have h2 : vecOf 1 = vecOf (ap12 (packR s12Rows) 1) := by
    rw [← isP_s12e.apply_code, h1]
    rfl
  have h3 := vecOf_inj (by norm_num) (ap12_lt _ _) h2
  rw [← h3] at hmove
  exact absurd hmove (by decide)

theorem sift17605 :
    Viol.genGrp pGens ≤ E0 ∧ Viol.genGrp E0Chk.sGensE0 ≤ E0 ∧ s12e ∉ E0 := by
  have key : ∀ r ∈ pGens ++ E0Chk.sGensE0, ∃ U ∈ E0, IsP U (packR r) := fun r hr => by
    obtain ⟨x, -, P, hP, hPF⟩ := exists_rec cf17605sift (List.mem_map.2 ⟨r, hr, rfl⟩)
    exact ⟨P * 1, mul_mem hP (one_mem _), hPF 1 IsP.one⟩
  refine ⟨genGrp_le (fun r hr => rowsP_packR r (by simp [hr])) fun r hr => key r (by simp [hr]),
    genGrp_le (fun r hr => rowsP_packR r (by simp [hr])) fun r hr => key r (by simp [hr]),
    s12e_not_mem_E0⟩

theorem sift17609 : Viol.genGrp sGens ≤ M0 ∧ Viol.genGrp lbarGens ≤ M0 := by
  have key : ∀ r ∈ sGens ++ lbarGens, ∃ U ∈ M0, IsP U (packR r) := fun r hr => by
    obtain ⟨x, hx, P, hP, hPF⟩ := exists_rec cf17609sift (List.mem_map.2 ⟨r, hr, rfl⟩)
    obtain ⟨Q, hQ, hQP, -⟩ := CFSG.KD.IF4M.exists_q x hx
    exact ⟨P * Q, mul_mem (CFSG.KD.IF4M.E0_le_M0 hP) hQ, hPF Q hQP⟩
  exact ⟨genGrp_le (fun r hr => rowsP_packR r (by simp [hr])) fun r hr => key r (by simp [hr]),
    genGrp_le (fun r hr => rowsP_packR r (by simp [hr])) fun r hr => key r (by simp [hr])⟩

theorem exists_lbar : ∀ l ∈ lbarGens, ∃ U ∈ Viol.genGrp lbarGens, IsP U (packR l) := by
  intro l hl
  have hsq := List.all_eq_true.1 cf17611aux.1 l hl
  rw [Nat.beq_eq] at hsq
  obtain ⟨U, hU⟩ := IsP.exists_of_mul hsq
  exact ⟨U, Subgroup.subset_closure
    ⟨l, hl, (isP_iff_of_rowsP (rowsP_packR l (by simp [hl])) U).1 hU⟩, hU⟩

theorem mem_E0_of_isP {U : GL} {m : Nat}
    (hm : m ∈ [packR (lbarGens.getD 3 #[]),
      mulP (packR (lbarGens.getD 0 #[])) (packR (lbarGens.getD 1 #[])),
      mulP (packR (lbarGens.getD 0 #[])) (packR (lbarGens.getD 2 #[])),
      mulP (packR (lbarGens.getD 0 #[])) (packR (lbarGens.getD 4 #[]))]) (hU : IsP U m) :
    U ∈ E0 := by
  obtain ⟨x, -, P, hP, hPF⟩ := exists_rec cf17611sift hm
  rw [hU.inj (hPF 1 IsP.one)]
  exact mul_mem hP (one_mem _)

theorem unitary_mem : ∀ l ∈ Viol.genGrp lbarGens, l * omegaE = omegaE * l → l ∈ E0 := by
  have hmem : ∀ j < 5, lbarGens.getD j #[] ∈ lbarGens := fun j hj => by
    interval_cases j <;> simp [lbarGens]
  have hL : ∀ j < 5, ∃ U ∈ Viol.genGrp lbarGens, IsP U (packR (lbarGens.getD j #[])) :=
    fun j hj => exists_lbar _ (hmem j hj)
  obtain ⟨A, hA, hAP⟩ := hL 0 (by norm_num)
  have hAM : A ∈ M0 := sift17609.2 hA
  have hA2 : A * A = 1 := by
    have hsq := List.all_eq_true.1 cf17611aux.1 _ (hmem 0 (by norm_num))
    rw [Nat.beq_eq] at hsq
    have := hAP.mul hAP
    rw [hsq] at this
    exact this.inj IsP.one
  have hgen : ∀ G ∈ Viol.GenSet lbarGens, G ∈ E0 ∨ A * G ∈ E0 := by
    rintro G ⟨r, hr, hG⟩
    have hGP : IsP G (packR r) := (isP_iff_of_rowsP (rowsP_packR r (by simp [hr])) G).2 hG
    have hr' : r = lbarGens.getD 0 #[] ∨ r = lbarGens.getD 1 #[] ∨ r = lbarGens.getD 2 #[] ∨
        r = lbarGens.getD 3 #[] ∨ r = lbarGens.getD 4 #[] := by
      simpa [lbarGens] using hr
    rcases hr' with h | h | h | h | h <;> rw [h] at hGP
    · right
      rw [hGP.inj hAP, hA2]
      exact one_mem _
    · exact Or.inr (mem_E0_of_isP (by simp) (hAP.mul hGP))
    · exact Or.inr (mem_E0_of_isP (by simp) (hAP.mul hGP))
    · exact Or.inl (mem_E0_of_isP (by simp) hGP)
    · exact Or.inr (mem_E0_of_isP (by simp) (hAP.mul hGP))
  have hcase : ∀ l ∈ Viol.genGrp lbarGens, l ∈ E0 ∨ A * l ∈ E0 := by
    intro l hl
    refine mem_of_closure (K := {g | g ∈ E0 ∨ A * g ∈ E0}) (Or.inl (one_mem _)) ?_ hl
    intro s hs y hy
    rcases hgen s hs with hs | hs <;> rcases hy with hy | hy
    · exact Or.inl (mul_mem hs hy)
    · right
      have e : A * (s * y) = (A * s * A⁻¹) * (A * y) := by group
      rw [e]
      exact mul_mem (CFSG.KD.IF4M.conj_mem_E0 hAM hs) hy
    · right
      rw [← mul_assoc]
      exact mul_mem hs hy
    · left
      have e : s * y = (A * (A * s) * A⁻¹) * (A * y) := by
        calc s * y = (A * A) * s * y := by rw [hA2, one_mul]
          _ = (A * (A * s) * A⁻¹) * (A * y) := by group
      rw [e]
      exact mul_mem (CFSG.KD.IF4M.conj_mem_E0 hAM hs) hy
  intro l hl hlc
  rcases hcase l hl with h | h
  · exact h
  · exfalso
    have hc : Commute (A * l * l⁻¹) omegaE :=
      Commute.mul_left (E0_comm_omegaE _ h) (Commute.inv_left hlc)
    rw [mul_inv_cancel_right] at hc
    have h1 := congrArg (fun U : GL => U (vecOf 64)) hc.eq
    rw [(hAP.mul isP_omegaE).apply_code, (isP_omegaE.mul hAP).apply_code] at h1
    have h2 := vecOf_inj (ap12_lt _ _) (ap12_lt _ _) h1
    have h3 := cf17611aux.2
    rw [h2, Nat.beq_refl] at h3
    exact Bool.false_ne_true h3.symm

theorem sift17611 :
    (∀ l ∈ Viol.genGrp lbarGens, ∀ e ∈ E0, l * e * l⁻¹ ∈ E0) ∧
    (∀ l ∈ Viol.genGrp lbarGens, l * omegaE = omegaE * l → l ∈ E0) ∧
    Viol.genGrp skGens ≤ E0 ⊔ Viol.genGrp lbarGens ∧ s12e ∉ E0 ⊔ Viol.genGrp lbarGens := by
  have hconj : ∀ l ∈ Viol.genGrp lbarGens, ∀ e ∈ E0, l * e * l⁻¹ ∈ E0 := fun l hl e he =>
    CFSG.KD.IF4M.conj_mem_E0 (sift17609.2 hl) he
  refine ⟨hconj, unitary_mem, ?_, ?_⟩
  · refine genGrp_le (fun r hr => rowsP_packR r (by simp [hr])) fun r hr => ?_
    obtain ⟨x, -, P, hP, hPF⟩ := exists_rec cf17611sk (List.mem_map.2 ⟨r, hr, rfl⟩)
    obtain ⟨F, hF, hFP⟩ := exists_subP (K := Viol.genGrp lbarGens) (lbarGens.map packR)
      (fun g hg => by
        obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hg
        exact exists_lbar l hl) x
    exact ⟨P * F, mul_mem (Subgroup.mem_sup_left hP) (Subgroup.mem_sup_right hF), hPF F hFP⟩
  · intro h
    have h' : s12e ∈ Subgroup.closure ((E0 : Set GL) ∪ Viol.genGrp lbarGens) := by
      rwa [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    obtain ⟨e, he, l, hl, hx⟩ : ∃ e ∈ E0, ∃ l ∈ Viol.genGrp lbarGens, s12e = e * l := by
      refine mem_of_closure (K := {g | ∃ e ∈ E0, ∃ l ∈ Viol.genGrp lbarGens, g = e * l})
        ⟨1, one_mem _, 1, one_mem _, by rw [mul_one]⟩ ?_ h'
      rintro s hs y ⟨e, he, l, hl, rfl⟩
      rcases hs with hs | hs
      · exact ⟨s * e, mul_mem hs he, l, hl, by rw [mul_assoc]⟩
      · exact ⟨s * e * s⁻¹, hconj s hs e he, s * l, mul_mem hs hl, by group⟩
    have hle : l = e⁻¹ * s12e := eq_inv_mul_of_mul_eq hx.symm
    have hlc : l * omegaE = omegaE * l := by
      rw [hle]
      exact (Commute.inv_left (E0_comm_omegaE e he)).mul_left s12e_comm_omegaE
    exact s12e_not_mem_E0 (hx ▸ mul_mem he (unitary_mem l hl hlc))

end CFSG.KD.IF4R

end
