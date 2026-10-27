module

public import Certificates.Kernel.LocalComp.WittA7041
public import Certificates.Kernel.LocalComp.WittK7103
public import Certificates.Kernel.M23Norm3.Checks

public section

namespace CertificateChecks.KernelM23Norm3

open Equiv CFSG.M23Norm3 CFSG.A7Fano CFSG.QuasithinUnique.Vol2Native.L239
open CFSG.KC.WCnt CFSG.KS.PCnt CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94
  CFSG.Quasithin.H13 CertificateChecks.KernelLC.Witt

theorem ker1_iff (σ : Fin 22 → Fin 22) : ker1P σ ↔ (∀ p ∈ m22HexadL, σ p ∈ m22HexadL) ∧
    (∀ p ∈ ([0, 1, 3, 6, 14, 20] : List (Fin 22)), σ p ∈ ([0, 1, 3, 6, 14, 20] : List (Fin 22))) ∧
    (∀ p ∈ ([0, 1, 4, 5, 13, 18] : List (Fin 22)), σ p ∈ ([0, 1, 4, 5, 13, 18] : List (Fin 22))) ∧
    (∀ p ∈ ([0, 1, 7, 8, 16, 21] : List (Fin 22)), σ p ∈ ([0, 1, 7, 8, 16, 21] : List (Fin 22))) ∧
    (∀ p ∈ ([0, 1, 10, 11, 12, 15] : List (Fin 22)),
      σ p ∈ ([0, 1, 10, 11, 12, 15] : List (Fin 22))) := by
  unfold ker1P
  constructor
  · intro h
    exact ⟨h _ (by decide), h _ (by decide), h _ (by decide), h _ (by decide), h _ (by decide)⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ l hl
    simp only [m22Hex01L, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl
    exacts [h0, h1, h2, h3, h4]

theorem ker2_iff (σ : Fin 22 → Fin 22) :
    ker2P σ ↔ σ 0 = 0 ∧ σ 1 = 1 ∧ σ 2 = 2 ∧ σ 9 = 9 ∧ σ 17 = 17 ∧ σ 19 = 19 := by
  simp [ker2P, m22HexadL]

theorem ker1_pkw (τ : Perm (Fin 22)) : (presT 655879 [0, 1, 2, 9, 17, 19] (pkw 5 τ) &&
    presT 1065035 [0, 1, 3, 6, 14, 20] (pkw 5 τ) && presT 270387 [0, 1, 4, 5, 13, 18] (pkw 5 τ) &&
    presT 2163075 [0, 1, 7, 8, 16, 21] (pkw 5 τ) && presT 39939 [0, 1, 10, 11, 12, 15] (pkw 5 τ)) =
      decide (ker1P ⇑τ) := by
  rw [presH_pkw,
    presL_pkw τ [0, 1, 3, 6, 14, 20] [0, 1, 3, 6, 14, 20] 1065035 (by decide +kernel) (by decide)
      (by decide +kernel),
    presL_pkw τ [0, 1, 4, 5, 13, 18] [0, 1, 4, 5, 13, 18] 270387 (by decide +kernel) (by decide)
      (by decide +kernel),
    presL_pkw τ [0, 1, 7, 8, 16, 21] [0, 1, 7, 8, 16, 21] 2163075 (by decide +kernel) (by decide)
      (by decide +kernel),
    presL_pkw τ [0, 1, 10, 11, 12, 15] [0, 1, 10, 11, 12, 15] 39939 (by decide +kernel) (by decide)
      (by decide +kernel),
    Bool.eq_iff_iff, decide_eq_true_iff, ker1_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem ker2_pkw (τ : Perm (Fin 22)) : (Nat.beq (pt (pkw 5 τ) 0) 0 && Nat.beq (pt (pkw 5 τ) 1) 1 &&
    Nat.beq (pt (pkw 5 τ) 2) 2 && Nat.beq (pt (pkw 5 τ) 9) 9 && Nat.beq (pt (pkw 5 τ) 17) 17 &&
    Nat.beq (pt (pkw 5 τ) 19) 19) = decide (ker2P ⇑τ) := by
  have e2 : Nat.beq (pt (pkw 5 τ) 2) 2 = decide (τ 2 = 2) := beq_pt_pkw τ 2 2
  have e9 : Nat.beq (pt (pkw 5 τ) 9) 9 = decide (τ 9 = 9) := beq_pt_pkw τ 9 9
  have e17 : Nat.beq (pt (pkw 5 τ) 17) 17 = decide (τ 17 = 17) := beq_pt_pkw τ 17 17
  have e19 : Nat.beq (pt (pkw 5 τ) 19) 19 = decide (τ 19 = 19) := beq_pt_pkw τ 19 19
  rw [beq0_pkw, beq1_pkw, e2, e9, e17, e19, Bool.eq_iff_iff, decide_eq_true_iff, ker2_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem count_borel :
    m22Count (fun σ => σ 0 = 0 ∧ σ 1 = 1 ∧ (∀ p ∈ m22HexadL, σ p ∈ m22HexadL) ∧
      (∀ x, σ (σ x) = x) ∧ ¬ ker1P σ ∧ ¬ ker2P σ) = 0 := by
  refine (m22Count_eq_wcB _ _ (fun τ => ?_) 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
    fun σ h => ?_).trans k7103
  · rw [ker1_pkw, ker2_pkw, beq0_pkw, beq1_pkw, presH_pkw, invT_pkw _ KernelSpor.M22Syl.pk_one,
      Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
      and_assoc]
  · rw [mul_one] at h
    rw [h.1, h.2.1]
    exact ⟨rfl, rfl, (mem_hexL _).2 (h.2.2.1 2 (by decide))⟩

theorem borel_of_bad (x : Fin 22 → Fin 22) (h : badBorel x = true) :
    x 0 = 0 ∧ x 1 = 1 ∧ (∀ p ∈ m22HexadL, x p ∈ m22HexadL) ∧ (∀ p, x (x p) = p) ∧
      ¬ ker1P x ∧ ¬ ker2P x := by
  by_cases hx : borelP x ∧ invP x ∧ ¬ ker1P x ∧ ¬ ker2P x
  · unfold borelP invP at hx
    obtain ⟨⟨h0, h1, h2⟩, h3, h4, h5⟩ := hx
    exact ⟨h0, h1, h2, h3, h4, h5⟩
  · rw [badBorel, if_neg hx] at h
    exact absurd h (by decide)

theorem m22Count_badBorel :
    m22Count (fun x => badBorel x = true) = 0 := by
  have h := count_borel
  rw [← card_m22_subtype] at h ⊢
  have he := Finite.card_eq_zero_iff.1 h
  exact Finite.card_eq_zero_iff.2 ⟨fun x => he.false ⟨x.1, borel_of_bad _ x.2⟩⟩

theorem even_vals {σ : Perm (Fin 7)} (h : Perm.sign σ = 1) :
    CFSG.Quasithin.B3.invCount (List.ofFn fun i => (σ i).val) % 2 = 0 := by
  have h' := (CFSG.Quasithin.B3.mem_alternatingGroup_iff σ).1 (Perm.mem_alternatingGroup.2 h)
  unfold CFSG.Quasithin.B3.isEvenT CFSG.Quasithin.B3.tab at h'
  exact beq_iff_eq.1 h'

theorem lt4 : ∀ x : Fin 7, x ≠ 4 → x ≠ 5 → x ≠ 6 → x.val < 4 := by decide +kernel

theorem mem_k4 (σ : Perm (Fin 7)) (hs : Perm.sign σ = 1) (h4 : σ ^ 4 = 1) (e4 : σ 4 = 4)
    (e5 : σ 5 = 5) (e6 : σ 6 = 6) : σ ∈ k4List := by
  have hlt : ∀ i : Fin 7, i.val < 4 → (σ i).val < 4 := by
    intro i hi
    refine lt4 _ (fun h => ?_) (fun h => ?_) (fun h => ?_)
    · have e := σ.injective (h.trans e4.symm)
      subst e
      exact absurd hi (by decide)
    · have e := σ.injective (h.trans e5.symm)
      subst e
      exact absurd hi (by decide)
    · have e := σ.injective (h.trans e6.symm)
      subst e
      exact absurd hi (by decide)
  have d : ∀ i j : Fin 7, i ≠ j → σ i ≠ σ j := fun i j h e => h (σ.injective e)
  have hv : ⇑σ = ![σ 0, σ 1, σ 2, σ 3, 4, 5, 6] := by
    funext i
    fin_cases i <;> first | rfl | exact e4 | exact e5 | exact e6
  have e : (4 : ℕ) = 1 + 1 + 1 + 1 := rfl
  rw [e, pow_add, pow_add, pow_add, pow_one] at h4
  have hp : ∀ i, σ (σ (σ (σ i))) = i := fun i => by
    have := Perm.ext_iff.1 h4 i
    simpa only [Perm.mul_apply, Perm.one_apply] using this
  obtain ⟨τ, hτ, he⟩ := k4_vals (σ 0) (hlt 0 (by decide)) (σ 1) (hlt 1 (by decide))
    (d 1 0 (by decide)) (σ 2) (hlt 2 (by decide)) (d 2 0 (by decide)) (d 2 1 (by decide))
    (σ 3) (hlt 3 (by decide)) (d 3 0 (by decide)) (d 3 1 (by decide)) (d 3 2 (by decide))
    (by rw [← hv]; exact even_vals hs) (by rw [← hv]; exact hp)
  have hστ : σ = τ := Equiv.ext fun i => (congrFun hv i).trans (he i)
  rw [hστ]
  exact hτ

theorem c33_vals : c33 0 = 0 ∧ c33 1 = 2 ∧ c33 2 = 3 ∧ c33 3 = 1 ∧ c33 4 = 5 ∧ c33 5 = 6 ∧
    c33 6 = 4 := by
  decide +kernel

theorem c33_fix : ∀ x : Fin 7, c33 x = x → x = 0 := by decide +kernel

theorem cent (σ : Perm (Fin 7)) (hs : Perm.sign σ = 1) (hc : σ * c33 = c33 * σ) :
    ∃ a b : Fin 3, σ = c33 ^ (a : ℕ) * c123 ^ (b : ℕ) := by
  have hc' : ∀ i, σ (c33 i) = c33 (σ i) := fun i => by
    have := Perm.ext_iff.1 hc i
    simpa only [Perm.mul_apply] using this
  obtain ⟨v0, v1, v2, -, v4, v5, -⟩ := c33_vals
  have s0 : σ 0 = 0 := c33_fix _ (by rw [← hc', v0])
  have s2 : σ 2 = c33 (σ 1) := by rw [← hc', v1]
  have s3 : σ 3 = c33 (c33 (σ 1)) := by rw [← s2, ← hc', v2]
  have s5 : σ 5 = c33 (σ 4) := by rw [← hc', v4]
  have s6 : σ 6 = c33 (c33 (σ 4)) := by rw [← s5, ← hc', v5]
  have hv : ⇑σ = ![0, σ 1, c33 (σ 1), c33 (c33 (σ 1)), σ 4, c33 (σ 4), c33 (c33 (σ 4))] := by
    funext i
    fin_cases i <;> first | rfl | exact s0 | exact s2 | exact s3 | exact s5 | exact s6
  obtain ⟨x, y, he⟩ := cent_vals (σ 1) (σ 4) (by rw [← hv]; exact fun i j h => σ.injective h)
    (by rw [← hv]; exact even_vals hs)
  exact ⟨x, y, Equiv.ext fun i => (congrFun hv i).trans (he i)⟩

end CertificateChecks.KernelM23Norm3

end
