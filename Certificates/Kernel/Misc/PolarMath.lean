
module

public import CFSG.Fischer.TransvectionPointsBase
import all CFSG.Fischer.F4

public section

namespace CFSG.KD.Misc.Polar

open CFSG.Fischer CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Matrix

attribute [local irreducible] CFSG.F4.Native.uPts ptIdx uVec

private theorem two_zero : (2 : F4) = 0 := by decide

private theorem neg_self' : ∀ a : F4, -a = a := by decide

theorem tvM_conj (u v : W) (hu : hermStd u u = 0) :
    tvM u * tvM v * tvM u = tvM ((tvM u).mulVec v) := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  rw [← mulVec_mulVec, ← mulVec_mulVec, tvM_mulVec, tvM_mulVec, tvM_mulVec, tvM_mulVec,
    tvM_mulVec]
  simp only [hermStd_add_left, hermStd_add_right, hermStd_smul_left, hermStd_smul_right, hu,
    hermStd_swap v u]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (hermStd x u * u i + hermStd x u * hermStd x v * 0) * two_zero

theorem tvM_comm (u v : W) (huv : hermStd u v = 0) : tvM u * tvM v = tvM v * tvM u := by
  have hvu : hermStd v u = 0 := by rw [hermStd_swap, huv]; ring
  rw [Matrix.ext_iff_mulVec]
  intro x
  rw [← mulVec_mulVec, ← mulVec_mulVec, tvM_mulVec, tvM_mulVec, tvM_mulVec, tvM_mulVec]
  simp only [hermStd_add_left, hermStd_smul_left, huv, hvu, mul_zero, add_zero]
  abel

theorem smul_of_ptIdx_eq {w w' : W} (hw : w ≠ 0) (hw' : w' ≠ 0) (hi : hermStd w w = 0)
    (hi' : hermStd w' w' = 0) (h : ptIdx w = ptIdx w') : ∃ c : F4, c ≠ 0 ∧ w' = c • w := by
  have e1 := uVec_ptIdx ptsFacts hw hi
  have e2 := uVec_ptIdx ptsFacts hw' hi'
  rw [h, e2] at e1
  obtain ⟨a, ha, hwa⟩ := normV_eq_smul hw
  obtain ⟨b, hb, hwb⟩ := normV_eq_smul hw'
  rw [hwa, hwb] at e1
  refine ⟨b⁻¹ * a, mul_ne_zero (inv_ne_zero hb) ha, ?_⟩
  rw [mul_smul, ← e1, smul_smul, inv_mul_cancel₀ hb, one_smul]

theorem herm_zero_of_fixed {x u : W} (hx : x ≠ 0) (hxi : hermStd x x = 0)
    (hu : hermStd u u = 0) (h : ptIdx (x + hermStd x u • u) = ptIdx x) : hermStd x u = 0 := by
  by_contra hc
  have hne : x + hermStd x u • u ≠ 0 := by
    have := mulVec_ne_zero (tvGL u hu) hx
    rwa [tvGL_val, tvM_mulVec] at this
  have hiso : hermStd (x + hermStd x u • u) (x + hermStd x u • u) = 0 := by
    have := isIsom_tvM hu x x
    rwa [herm_eq_std, herm_eq_std, tvM_mulVec, hxi] at this
  obtain ⟨c, hc0, hcx⟩ := smul_of_ptIdx_eq hx hne hxi hiso h.symm
  have hu' : hermStd x u • u = (c + 1) • x := by
    have e : hermStd x u • u = c • x - x := by rw [← hcx]; abel
    rw [e]
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg, neg_self', add_mul,
      one_mul]
  have : hermStd x (hermStd x u • u) = hermStd x ((c + 1) • x) := by rw [hu']
  rw [hermStd_smul_right, hermStd_smul_right, hxi, mul_zero] at this
  exact hc (by
    have h2 := mul_eq_zero.1 this
    rcases h2 with h2 | h2
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
    · exact h2)

theorem tvP_val (p x : Fin 693) :
    (tvP p x).val = ptIdx (uVec x + hermStd (uVec x) (uVec p) • uVec p) := by
  rw [tvP, piSU_apply]
  exact congrArg ptIdx (tvM_mulVec _ _)

theorem uVec_tvP (p q : Fin 693) :
    uVec (tvP p q) = normV ((tvM (uVec p)).mulVec (uVec q)) := by
  have hw := mulVec_ne_zero (tvGL (uVec p) (uVec_iso ptsFacts p.2)) (uVec_ne_zero ptsFacts q.2)
  rw [tvGL_val] at hw
  have hi : hermStd ((tvM (uVec p)).mulVec (uVec q)) ((tvM (uVec p)).mulVec (uVec q)) = 0 := by
    have := isIsom_tvM (uVec_iso ptsFacts p.2) (uVec q) (uVec q)
    rwa [herm_eq_std, herm_eq_std, uVec_iso ptsFacts q.2] at this
  rw [← uVec_ptIdx ptsFacts hw hi, tvP_val, tvM_mulVec]

theorem tvP_conj' (p q : Fin 693) : tvP p * tvP q * tvP p = tvP (tvP p q) := by
  rw [tvP, tvP, tvP, ← map_mul, ← map_mul]
  refine congrArg piSU ?_
  apply Subtype.ext
  apply Units.ext
  change tvM (uVec p) * tvM (uVec q) * tvM (uVec p) = tvM (uVec (tvP p q))
  rw [tvM_conj _ _ (uVec_iso ptsFacts p.2), uVec_tvP]
  have hw := mulVec_ne_zero (tvGL (uVec p) (uVec_iso ptsFacts p.2)) (uVec_ne_zero ptsFacts q.2)
  rw [tvGL_val] at hw
  obtain ⟨c, hc, hcw⟩ := normV_eq_smul hw
  rw [hcw, tvM_smul' hc]

theorem tvP_sq (p : Fin 693) : tvP p * tvP p = 1 := by
  rw [tvP, ← map_mul, ← map_one piSU]
  refine congrArg piSU ?_
  apply Subtype.ext
  apply Units.ext
  change tvM (uVec p) * tvM (uVec p) = 1
  exact tvM_mul_self (uVec_iso ptsFacts p.2)

theorem tvP_comm_of (p q : Fin 693) (h : hermStd (uVec p) (uVec q) = 0) :
    tvP p * tvP q = tvP q * tvP p := by
  rw [tvP, tvP, ← map_mul, ← map_mul]
  refine congrArg piSU ?_
  apply Subtype.ext
  apply Units.ext
  change tvM (uVec p) * tvM (uVec q) = tvM (uVec q) * tvM (uVec p)
  exact tvM_comm _ _ h

theorem tvP_fix (p x : Fin 693) : tvP p x = x ↔ hermStd (uVec x) (uVec p) = 0 := by
  constructor
  · intro h
    have h' := congrArg Fin.val h
    rw [tvP_val] at h'
    exact herm_zero_of_fixed (uVec_ne_zero ptsFacts x.2) (uVec_iso ptsFacts x.2)
      (uVec_iso ptsFacts p.2) (h'.trans (ptIdx_uVec ptsFacts x.2).symm)
  · intro h
    apply Fin.ext
    rw [tvP_val, h, zero_smul, add_zero, ptIdx_uVec ptsFacts x.2]

theorem herm_swap_zero {x y : W} (h : hermStd x y = 0) : hermStd y x = 0 := by
  rw [hermStd_swap, h]
  ring

theorem tvP_inj (hw : ∀ p q : Fin 693, p < q → ∃ x : Fin 693,
      (hermStd (uVec x) (uVec p) = 0 ∧ hermStd (uVec x) (uVec q) ≠ 0) ∨
      (hermStd (uVec x) (uVec q) = 0 ∧ hermStd (uVec x) (uVec p) ≠ 0)) :
    Function.Injective tvP := by
  have key : ∀ p q : Fin 693, p < q → tvP p ≠ tvP q := by
    intro p q hpq he
    obtain ⟨x, hx | hx⟩ := hw p q hpq
    · exact hx.2 ((tvP_fix q x).1 (he ▸ (tvP_fix p x).2 hx.1))
    · exact hx.2 ((tvP_fix p x).1 (he.symm ▸ (tvP_fix q x).2 hx.1))
  intro p q he
  rcases lt_trichotomy p q with h | h | h
  · exact absurd he (key p q h)
  · exact h
  · exact absurd he.symm (key q p h)

theorem tvP_comm_iff (hw : ∀ p q : Fin 693, p < q → ∃ x : Fin 693,
      (hermStd (uVec x) (uVec p) = 0 ∧ hermStd (uVec x) (uVec q) ≠ 0) ∨
      (hermStd (uVec x) (uVec q) = 0 ∧ hermStd (uVec x) (uVec p) ≠ 0)) (p q : Fin 693) :
    tvP p * tvP q = tvP q * tvP p ↔ hermStd (uVec p) (uVec q) = 0 := by
  refine ⟨fun h => ?_, tvP_comm_of p q⟩
  have h1 : tvP (tvP p q) = tvP q := by
    rw [← tvP_conj', h, mul_assoc, tvP_sq, mul_one]
  have h2 := tvP_inj hw h1
  exact herm_swap_zero ((tvP_fix p q).1 h2)

end CFSG.KD.Misc.Polar

end
