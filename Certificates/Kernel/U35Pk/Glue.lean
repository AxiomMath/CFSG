module

public import CFSG.Quasithin.H13.NQCatT513U35Y
public import CFSG.Certificates.Kernel.U35Pk.Sound

public section

namespace CertificateChecks.U35Pk

open CFSG.Quasithin.H13.NQCat.T513.U35 HNUnitaryBridge CFSG.RankThree.PartOne.HNB Matrix
open CFSG.Quasithin.H13.KGU35 (f25Data suMat suMat_apply suMat_injective mem_SU)
open CFSG.Quasithin.H13.KGAutSyl.U35Syl (Rm Sm RR SS coe_RR coe_SS)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts

abbrev Mat3 : Type := Matrix (Fin 3) (Fin 3) F25

@[expose] def ctr (M : Mat3) : Mat3 := (M.map (· ^ 5))ᵀ

@[expose] def tHat : Set Mat3 := {T | ∃ i < 8, ∃ e < 2, T = Rm ^ i * Sm ^ e}

@[expose] def InScT (X : Mat3) : Prop := ∃ T ∈ tHat, ∃ c : F25, X = c • T

structure Facts {ι : Type} (U : ι → Mat3) (nHat : Set Mat3) : Prop where
  unitary_U : ∀ i, ctr (U i) * U i = 1
  n_block : ∀ s ∈ nHat, s 0 2 = 0 ∧ s 1 2 = 0 ∧ s 2 0 = 0 ∧ s 2 1 = 0 ∧ s 2 2 = 1
  n_unitary : ∀ s ∈ nHat, ctr s * s = 1
  n_norm : ∀ s ∈ nHat, ∀ T ∈ tHat, InScT (s * T * ctr s)
  cov : ∀ v : Fin 3 → F25, ∑ r, v r ^ 5 * v r = 1 →
    ∃ s ∈ nHat, ∃ i, ∃ l : F25, l ^ 6 = 1 ∧ s *ᵥ v = l • (U i)ᵀ 2
  elt : ∀ i, ∀ W : Mat3, ctr W * W = 1 → W 0 2 = 0 → W 1 2 = 0 → W 2 0 = 0 → W 2 1 = 0 →
    W 2 2 = 1 → ∃ o, 0 < o ∧ (∃ c : F25, (U i * W) ^ o = c • 1) ∧
      (∀ m, 0 < m → m < o → ¬ ∃ c : F25, (U i * W) ^ m = c • 1) ∧
      (Odd o → ((U i * W) 0 2 = 0 ∧ (U i * W) 1 2 = 0 ∧ (U i * W) 2 0 = 0 ∧
          (U i * W) 2 1 = 0 ∧ o ≠ 5) ∨
        ∃ t ∈ ({Sm, Rm, Rm ^ 2} : Set Mat3), ∀ k < o, ¬ InScT ((U i * W) ^ k * t * (U i * W)))
  t_indep : ∀ i < 8, ∀ e < 2, ∀ i' < 8, ∀ e' < 2,
    (∃ c : F25, Rm ^ i * Sm ^ e = c • (Rm ^ i' * Sm ^ e')) → i = i' ∧ e = e'
  t_center : ∀ i < 8, ∀ e < 2,
    (∃ c : F25, Rm * (Rm ^ i * Sm ^ e) = c • (Rm ^ i * Sm ^ e * Rm)) →
    (∃ c : F25, Sm * (Rm ^ i * Sm ^ e) = c • (Rm ^ i * Sm ^ e * Sm)) →
      (∃ c : F25, Rm ^ i * Sm ^ e = c • 1) ∨ ∃ c : F25, Rm ^ i * Sm ^ e = c • Rm ^ 4

abbrev PermT0 (x : MulAut PU) : Prop :=
  ∀ t ∈ T0, ∃ a : ℤ, ∃ t' ∈ T0, MulAut.conj t * x = x ^ a * MulAut.conj t'

theorem proj_eq_of_smul {g g' : ↥SU} {c : F25} (h : suMat g = c • suMat g') :
    proj g = proj g' := by
  refine proj_eq_iff.mpr ⟨c, ?_, h⟩
  rintro rfl
  rw [zero_smul, suMat_apply] at h
  exact (g : GL (Fin 3) F25).ne_zero h

theorem RRSS_mem_T0 (i e : ℕ) : proj (RR ^ i * SS ^ e) ∈ T0 :=
  ⟨_, mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
    (pow_mem (Subgroup.subset_closure (by simp)) _), rfl⟩

theorem suMat_RR : suMat RR = Rm := by rw [suMat_apply, coe_RR]

theorem suMat_SS : suMat SS = Sm := by rw [suMat_apply, coe_SS]

theorem smul_one_eq_scalar (c : F25) : c • (1 : Mat3) = Matrix.scalar (Fin 3) c := by
  rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem exists_isom {M : Mat3} (hM : ctr M * M = 1) : ∃ A : unitaryIsom3 f25Data, mat A = M := by
  have hmap : M.map f25Data.bar = M.map (· ^ 5) := by
    ext i k
    simp [f25_bar]
  refine ⟨⟨⟨M, ctr M, mul_eq_one_comm.mp hM, hM⟩, ?_⟩, rfl⟩
  rw [mem_unitaryIsom3]
  change (M.map f25Data.bar)ᵀ * M = 1
  rw [hmap]
  exact hM

theorem mat_mul (A B : unitaryIsom3 f25Data) : mat (A * B) = mat A * mat B := rfl

theorem mat_one : mat (1 : unitaryIsom3 f25Data) = 1 := rfl

theorem mat_inv_mul (A : unitaryIsom3 f25Data) : mat A⁻¹ * mat A = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

theorem mat_inv_eq {A : unitaryIsom3 f25Data} : mat A⁻¹ = ctr (mat A) :=
  (Matrix.inv_eq_left_inv (mat_inv_mul A)).symm.trans (Matrix.inv_eq_left_inv (unitary_mat A))

theorem fix_z0_of_block {B : unitaryIsom3 f25Data} (b02 : mat B 0 2 = 0) (b12 : mat B 1 2 = 0)
    (b20 : mat B 2 0 = 0) (b21 : mat B 2 1 = 0) : psuConj f25Data B z0 = z0 := by
  have hinv : mat B * (((B : GL (Fin 3) F25)⁻¹ : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) =
      1 := by
    rw [mat, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcomm : mat B * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] =
      !![-1, 0, 0; 0, -1, 0; 0, 0, 1] * mat B := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, b02, b12, b20, b21]
  have hfix : suConj f25Data B (RR ^ 4) = RR ^ 4 := by
    apply suMat_injective
    rw [suMat_suConj, suMat_RR4, ← mat, hcomm, Matrix.mul_assoc, hinv, Matrix.mul_one]
  rw [z0, psuConj_proj, hfix]

theorem orderOf_eq_of {B : unitaryIsom3 f25Data} {o : ℕ} (ho : 0 < o)
    (h1 : ∃ c : F25, mat B ^ o = c • 1) (h2 : ∀ m, 0 < m → m < o → ¬ ∃ c : F25, mat B ^ m = c • 1) :
    orderOf (psuConj f25Data B) = o := by
  rw [orderOf_eq_iff ho]
  refine ⟨(psuConj_pow_eq_one_iff B o).mpr ?_, fun m hm hm0 h => h2 m hm0 hm ?_⟩
  · obtain ⟨c, hc⟩ := h1
    exact ⟨c, by rw [hc, smul_one_eq_scalar]⟩
  · obtain ⟨c, hc⟩ := (psuConj_pow_eq_one_iff B m).mp h
    exact ⟨c, by rw [hc, smul_one_eq_scalar]⟩

theorem false_of_refute {B : unitaryIsom3 f25Data} {o : ℕ} (ho : orderOf (psuConj f25Data B) = o)
    (ho0 : 0 < o) (hperm : PermT0 (psuConj f25Data B)) {t : Mat3}
    (ht : t ∈ ({Sm, Rm, Rm ^ 2} : Set Mat3))
    (href : ∀ k < o, ¬ InScT (mat B ^ k * t * mat B)) : False := by
  obtain ⟨g, hg, rfl⟩ : ∃ g : ↥SU, g ∈ tT0 ∧ suMat g = t := by
    rcases ht with rfl | rfl | rfl
    · exact ⟨SS, Subgroup.subset_closure (by simp), suMat_SS⟩
    · exact ⟨RR, Subgroup.subset_closure (by simp), suMat_RR⟩
    · refine ⟨RR ^ 2, pow_mem (Subgroup.subset_closure (by simp)) 2, ?_⟩
      have h := suMat_RR_SS 2 0
      rwa [pow_zero, mul_one, pow_zero, mul_one] at h
  obtain ⟨a, t', ht', hta⟩ := hperm _ ⟨g, hg, rfl⟩
  obtain ⟨g'', hg'', rfl⟩ := ht'
  set x := psuConj f25Data B with hx
  have hj0 : (0 : ℤ) < o := by exact_mod_cast ho0
  have hxj : x ^ (o : ℤ) = 1 := by rw [zpow_natCast, ← ho, pow_orderOf_eq_one]
  set k := ((-a) % (o : ℤ)).toNat with hkdef
  have hk0 : ((k : ℕ) : ℤ) = (-a) % (o : ℤ) := by
    rw [hkdef]
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ hj0.ne')
  have hkj : k < o := by
    have := Int.emod_lt_of_pos (-a) hj0
    omega
  have hxk : x ^ k = (x ^ a)⁻¹ := by
    rw [← zpow_natCast, hk0, ← zpow_eq_zpow_emod (-a) hxj, _root_.zpow_neg]
  have hkey : x ^ k * MulAut.conj (proj g) * x = MulAut.conj (proj g'') := by
    rw [mul_assoc, hta, ← mul_assoc, hxk, inv_mul_cancel, one_mul]
  rw [conj_proj, conj_proj, hx, ← map_pow, ← map_mul, ← map_mul] at hkey
  set G : unitaryIsom3 f25Data := ⟨_, unitarySU_le_unitaryIsom3 g.2⟩ with hG
  set G'' : unitaryIsom3 f25Data := ⟨_, unitarySU_le_unitaryIsom3 g''.2⟩ with hG''
  have hkey' : psuConj f25Data (G''⁻¹ * (B ^ k * G * B)) = 1 := by
    rw [map_mul, hkey, map_inv, inv_mul_cancel]
  obtain ⟨-, c, -, hcB⟩ := eq_one_of_psuConj_mul_psuField_eq_one (G''⁻¹ * (B ^ k * G * B)) 1
    (by rw [map_one, mul_one, hkey'])
  have hmat : mat B ^ k * suMat g * mat B = (c : F25) • suMat g'' := by
    have e : ((B ^ k * G * B : unitaryIsom3 f25Data) : GL (Fin 3) F25) =
        (G'' : GL (Fin 3) F25) * Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
      rw [← hcB, ← Subgroup.coe_mul, mul_inv_cancel_left]
    have e2 := congrArg (fun g : GL (Fin 3) F25 => (g : Matrix (Fin 3) (Fin 3) F25)) e
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at e2
    rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one] at e2
    rw [← mat_pow, suMat_apply, suMat_apply]
    exact e2
  obtain ⟨i, hi, e, he, rfl⟩ := mem_tT0 hg''
  exact href k hkj ⟨_, ⟨i, hi, e, he, rfl⟩, c, by rw [hmat, suMat_RR_SS]⟩

section Facts

variable {ι : Type} {U : ι → Mat3} {nHat : Set Mat3}

theorem mem_T0_of_n (hF : Facts U nHat) {S : unitaryIsom3 f25Data} (hS : mat S ∈ nHat) {t : PU}
    (ht : t ∈ T0) : psuConj f25Data S t ∈ T0 := by
  obtain ⟨g, hg, rfl⟩ := ht
  obtain ⟨i, hi, e, he, rfl⟩ := mem_tT0 hg
  obtain ⟨T', ⟨j, -, f, -, rfl⟩, c, hc⟩ :=
    hF.n_norm _ hS (Rm ^ i * Sm ^ e) ⟨i, hi, e, he, rfl⟩
  have hc' : suMat (suConj f25Data S (RR ^ i * SS ^ e)) = c • suMat (RR ^ j * SS ^ f) := by
    rw [suMat_suConj, suMat_RR_SS, suMat_RR_SS]
    rw [← mat_inv_eq] at hc
    exact hc
  rw [psuConj_proj, proj_eq_of_smul hc']
  exact RRSS_mem_T0 j f

theorem fix_z0_of_n (hF : Facts U nHat) {S : unitaryIsom3 f25Data} (hS : mat S ∈ nHat) :
    psuConj f25Data S z0 = z0 := by
  obtain ⟨b02, b12, b20, b21, -⟩ := hF.n_block _ hS
  exact fix_z0_of_block b02 b12 b20 b21

theorem conj_mulAut (ψ : MulAut PU) (y : PU) :
    MulAut.conj (ψ y) = ψ * MulAut.conj y * ψ⁻¹ := by
  ext w
  simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem permT0_conj {ψ : MulAut PU} (hψ : ∀ t ∈ T0, ψ t ∈ T0) {x : MulAut PU}
    (hperm : PermT0 x) : PermT0 (ψ * x * ψ⁻¹) := by
  have hsurj : ∀ t ∈ T0, ∃ t₁ ∈ T0, ψ t₁ = t := by
    have hinj : Function.Injective (fun t : ↥T0 => (⟨ψ t, hψ t t.2⟩ : ↥T0)) := by
      intro t t' h
      exact Subtype.ext (ψ.injective (congrArg Subtype.val h))
    intro t ht
    obtain ⟨t₁, ht₁⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨t, ht⟩
    exact ⟨t₁, t₁.2, congrArg Subtype.val ht₁⟩
  intro t ht
  obtain ⟨t₁, ht₁, rfl⟩ := hsurj t ht
  obtain ⟨a, t', ht', hta⟩ := hperm t₁ ht₁
  refine ⟨a, ψ t', hψ t' ht', ?_⟩
  have e3 : (ψ * x * ψ⁻¹) ^ a = ψ * x ^ a * ψ⁻¹ := conj_zpow
  rw [conj_mulAut, conj_mulAut, e3]
  calc ψ * MulAut.conj t₁ * ψ⁻¹ * (ψ * x * ψ⁻¹) = ψ * (MulAut.conj t₁ * x) * ψ⁻¹ := by group
    _ = ψ * (x ^ a * MulAut.conj t') * ψ⁻¹ := by rw [hta]
    _ = ψ * x ^ a * ψ⁻¹ * (ψ * MulAut.conj t' * ψ⁻¹) := by group

theorem mulVec_e2 (M : Mat3) : M *ᵥ Pi.single 2 1 = Mᵀ 2 := Matrix.mulVec_single_one M 2

theorem exists_reduce (hF : Facts U nHat) (A : unitaryIsom3 f25Data) :
    ∃ S : unitaryIsom3 f25Data, mat S ∈ nHat ∧ ∃ A' : unitaryIsom3 f25Data, ∃ i, ∃ W : Mat3,
      ctr W * W = 1 ∧ W 0 2 = 0 ∧ W 1 2 = 0 ∧ W 2 0 = 0 ∧ W 2 1 = 0 ∧ W 2 2 = 1 ∧
      mat A' = U i * W ∧
      psuConj f25Data A' = psuConj f25Data S * psuConj f25Data A * (psuConj f25Data S)⁻¹ := by
  have hv : ∑ r, (mat A)ᵀ 2 r ^ 5 * (mat A)ᵀ 2 r = 1 := by
    have h := congrFun (congrFun (unitary_mat A) 2) 2
    simpa [Matrix.mul_apply] using h
  obtain ⟨s, hs, i, l, hl6, hsv⟩ := hF.cov _ hv
  obtain ⟨S, rfl⟩ := exists_isom (hF.n_unitary s hs)
  obtain ⟨UU, hUU⟩ := exists_isom (hF.unitary_U i)
  have hl0 : l ≠ 0 := by
    rintro rfl
    norm_num at hl6
  have hl6' : l⁻¹ ^ 6 = 1 := by rw [inv_pow, hl6, inv_one]
  have hl0' : l⁻¹ ≠ 0 := inv_ne_zero hl0
  set L : unitaryIsom3 f25Data := ⟨_, scalar_mem_isom hl6' hl0'⟩ with hL
  set A' : unitaryIsom3 f25Data := L * (S * A * S⁻¹) with hA'
  have hmatA' : mat A' = l⁻¹ • (mat S * mat A * ctr (mat S)) := by
    rw [hA', mat_mul, mat_mul, mat_mul, mat_inv_eq, mat, hL, Matrix.GeneralLinearGroup.coe_scalar,
      Units.val_mk0, ← smul_one_eq_scalar, Matrix.smul_mul, one_mul]
  obtain ⟨b02, b12, b20, b21, b22⟩ := hF.n_block _ hs
  have hSe : ctr (mat S) *ᵥ Pi.single 2 1 = Pi.single 2 1 := by
    rw [mulVec_e2]
    funext r
    fin_cases r <;> simp [ctr, b20, b21, b22]
  have hA'e : mat A' *ᵥ Pi.single 2 1 = mat UU *ᵥ Pi.single 2 1 := by
    rw [hmatA', Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hSe, ← Matrix.mulVec_mulVec,
      mulVec_e2, hsv, smul_smul, inv_mul_cancel₀ hl0, one_smul, hUU, mulVec_e2]
  set W := mat (UU⁻¹ * A') with hW
  have hWe : W *ᵥ Pi.single 2 1 = Pi.single 2 1 := by
    rw [hW, mat_mul, ← Matrix.mulVec_mulVec, hA'e, Matrix.mulVec_mulVec, mat_inv_mul,
      Matrix.one_mulVec]
  rw [mulVec_e2] at hWe
  have w02 : W 0 2 = 0 := by simpa using congrFun hWe 0
  have w12 : W 1 2 = 0 := by simpa using congrFun hWe 1
  have w22 : W 2 2 = 1 := by simpa using congrFun hWe 2
  have hWu : ctr W * W = 1 := unitary_mat _
  have w20 : W 2 0 = 0 := by
    have h := congrFun (congrFun hWu 2) 0
    simpa [ctr, Matrix.mul_apply, Fin.sum_univ_three, w02, w12, w22] using h
  have w21 : W 2 1 = 0 := by
    have h := congrFun (congrFun hWu 2) 1
    simpa [ctr, Matrix.mul_apply, Fin.sum_univ_three, w02, w12, w22] using h
  refine ⟨S, hs, A', i, W, hWu, w02, w12, w20, w21, w22, ?_, ?_⟩
  · rw [hW, ← hUU, ← mat_mul, mul_inv_cancel_left]
  · rw [hA', map_mul, hL, psuConj_scalar, one_mul, map_mul, map_mul, map_inv]

theorem main_of_facts (hF : Facts U nHat) {x : MulAut PU} (hx : x ∈ (psuConj f25Data).range)
    (hodd : Odd (orderOf x)) (hperm : PermT0 x) : x z0 = z0 ∧ orderOf x ≠ 5 := by
  obtain ⟨A, rfl⟩ := hx
  obtain ⟨S, hS, A', i, W, hWu, w02, w12, w20, w21, w22, hA'W, hA'⟩ := exists_reduce hF A
  set ψ := psuConj f25Data S with hψ
  have hord : orderOf (psuConj f25Data A') = orderOf (psuConj f25Data A) := by
    rw [hA', ← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have hperm' : PermT0 (psuConj f25Data A') := by
    rw [hA']
    exact permT0_conj (fun t ht => mem_T0_of_n hF hS ht) hperm
  obtain ⟨o, ho, h1, h2, h3⟩ := hF.elt i W hWu w02 w12 w20 w21 w22
  rw [← hA'W] at h1 h2 h3
  have hoA' := orderOf_eq_of ho h1 h2
  rcases h3 (hoA' ▸ hord ▸ hodd) with ⟨b02, b12, b20, b21, ho5⟩ | ⟨t, ht, href⟩
  · refine ⟨?_, by rw [← hord, hoA']; exact ho5⟩
    have hfix := fix_z0_of_block b02 b12 b20 b21
    rw [hA', MulAut.mul_apply, MulAut.mul_apply] at hfix
    have hz := fix_z0_of_n hF hS
    have hzi : ψ⁻¹ z0 = z0 := by
      nth_rewrite 1 [← hz]
      rw [MulAut.inv_apply_self]
    rw [hzi] at hfix
    exact ψ.injective (hfix.trans hz.symm)
  · exact (false_of_refute hoA' ho hperm' ht href).elim

theorem card_T0_of_facts (hF : Facts U nHat) : Nat.card T0 = 16 := by
  set S : Finset (ℕ × ℕ) := Finset.range 8 ×ˢ Finset.range 2 with hSdef
  have himg : (T0 : Set PU) = (fun p : ℕ × ℕ => proj (RR ^ p.1 * SS ^ p.2)) '' ↑S := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨i, hi, e, he, rfl⟩ := mem_tT0 hg
      exact ⟨(i, e), by simp [hSdef, hi, he], rfl⟩
    · rintro ⟨⟨i, e⟩, -, rfl⟩
      exact RRSS_mem_T0 i e
  have hinj : Set.InjOn (fun p : ℕ × ℕ => proj (RR ^ p.1 * SS ^ p.2)) ↑S := by
    rintro ⟨i, e⟩ hp ⟨i', e'⟩ hp' h
    simp only [hSdef, Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio] at hp hp'
    obtain ⟨c, -, hc⟩ := proj_eq_iff.mp h
    rw [suMat_RR_SS, suMat_RR_SS] at hc
    obtain ⟨rfl, rfl⟩ := hF.t_indep i hp.1 e hp.2 i' hp'.1 e' hp'.2 ⟨c, hc⟩
    rfl
  have h1 : Nat.card T0 = Nat.card ((fun p : ℕ × ℕ => proj (RR ^ p.1 * SS ^ p.2)) '' ↑S) := by
    rw [← himg]
    rfl
  rw [h1, Nat.card_image_of_injOn hinj, Nat.card_coe_set_eq, Set.ncard_coe_finset, hSdef,
    Finset.card_product, Finset.card_range, Finset.card_range]

theorem center_T0_of_facts (hF : Facts U nHat) {x : PU} (hx : x ∈ T0)
    (hc : ∀ y ∈ T0, x * y = y * x) : x = 1 ∨ x = z0 := by
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨i, hi, e, he, rfl⟩ := mem_tT0 hg
  have key : ∀ h : ↥SU, proj h ∈ T0 →
      ∃ c : F25, suMat h * (Rm ^ i * Sm ^ e) = c • (Rm ^ i * Sm ^ e * suMat h) := by
    intro h hh
    have h1 := hc _ hh
    rw [← map_mul, ← map_mul] at h1
    obtain ⟨c, -, hc'⟩ := proj_eq_iff.mp h1.symm
    simp only [map_mul, map_pow, suMat_RR, suMat_SS] at hc'
    exact ⟨c, hc'⟩
  have hR := key RR RR_mem_T0
  have hS := key SS SS_mem_T0
  rw [suMat_RR] at hR
  rw [suMat_SS] at hS
  rcases hF.t_center i hi e he hR hS with ⟨c, hc1⟩ | ⟨c, hc4⟩
  · left
    rw [← map_one proj]
    exact proj_eq_of_smul (by rw [suMat_RR_SS, map_one]; exact hc1)
  · right
    exact proj_eq_of_smul (by rw [suMat_RR_SS, map_pow, suMat_RR]; exact hc4)

open CFSG.Quasithin.H13.NQCat.T513 CFSG.RankThree.PartTwo.KFacts in
theorem certificate7159_of_facts (hF : Facts U nHat) : Nat.card ↥U35.T0 = 16 ∧
    (∀ x ∈ U35.T0, (∀ y ∈ U35.T0, x * y = y * x) → x = 1 ∨ x = U35.z0) ∧
    ∀ x ∈ (psuConj CFSG.Quasithin.H13.KGU35.f25Data).range, Odd (orderOf x) →
      (∀ t ∈ U35.T0, ∃ a : ℤ, ∃ t' ∈ U35.T0, MulAut.conj t * x = x ^ a * MulAut.conj t') →
        x U35.z0 = U35.z0 :=
  ⟨card_T0_of_facts hF, fun _ hx hc => center_T0_of_facts hF hx hc,
    fun _ hx hodd hperm => (main_of_facts hF hx hodd hperm).1⟩

open CFSG.Quasithin.H13.NQCat.T513 CFSG.RankThree.PartTwo.KFacts in
theorem certificate7170_of_facts (hF : Facts U nHat) : Nat.card ↥U35.T0 = 16 ∧
    ∀ x ∈ (psuConj CFSG.Quasithin.H13.KGU35.f25Data).range, orderOf x = 5 →
      ¬ ∀ t ∈ U35.T0, ∃ a : ℤ, ∃ t' ∈ U35.T0, MulAut.conj t * x = x ^ a * MulAut.conj t' :=
  ⟨card_T0_of_facts hF,
    fun _ hx h5 hperm => (main_of_facts hF hx (by rw [h5]; decide) hperm).2 h5⟩

end Facts

theorem facts_of_sound {ι : Type} {U : ι → Mat3} {nHat : Set Mat3}
    (h : CFSG.Certificates.U35Pk.SoundFacts U nHat) : Facts U nHat :=
  ⟨h.unitary_U, h.n_block, h.n_unitary, h.n_norm, h.cov, h.elt, h.t_indep, h.t_center⟩

end CertificateChecks.U35Pk
