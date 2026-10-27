
module

public import CFSG.GF2Type.Smith1979.IdxFourModelLemma5Base

public section

namespace CFSG.KD.IF4X

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.IdxFour

@[expose] noncomputable def trvL : V12 →ₗ[ZMod 2] V12 where
  toFun v := v + f0 v (theta0 w0) • w0 + f0 v w0 • theta0 w0
  map_add' x y := by
    simp only [f0_add_left, add_smul]
    abel
  map_smul' c x := by
    have hs : ∀ y, f0 (c • x) y = c * f0 x y := fun y => by
      unfold f0
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    simp only [hs, mul_smul, smul_add, RingHom.id_apply]

theorem vecOf_bif (b : Bool) (a : ℕ) :
    vecOf (bif b then a else 0) = (if b then (1 : ZMod 2) else 0) • vecOf a := by
  cases b <;> simp

theorem s12_basis : ∀ i : Fin 12, appN s12Rows (2 ^ i.val) =
    2 ^ i.val ^^^ (bif f0b (2 ^ i.val) 192 then 3 else 0) ^^^
      (bif f0b (2 ^ i.val) 3 then 192 else 0) := by
  decide +kernel

theorem vecOf_two_pow : ∀ i : Fin 12, vecOf (2 ^ i.val) = Pi.single i 1 := by
  decide +kernel

theorem x0_formula (v : V12) : x0 v = v + f0 v (theta0 w0) • w0 + f0 v w0 • theta0 w0 := by
  have h : x0.toLinearMap = trvL := by
    refine (Pi.basisFun (ZMod 2) (Fin 12)).ext fun i => ?_
    rw [Pi.basisFun_apply, ← vecOf_two_pow i]
    change x0 (vecOf (2 ^ i.val)) = vecOf (2 ^ i.val) + f0 (vecOf (2 ^ i.val)) (theta0 w0) • w0 +
      f0 (vecOf (2 ^ i.val)) w0 • theta0 w0
    have hlt : 2 ^ i.val < 4096 := lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) i.2)
      (by norm_num)
    rw [x0_apply_code, codeOf_vecOf hlt, s12_basis, vecOf_xor, vecOf_xor, vecOf_bif, vecOf_bif,
      theta0_w0, w0, f0_vecOf, f0_vecOf]
  exact LinearMap.congr_fun h v

theorem stabIn_M0_w0_le {U : V12 ≃ₗ[ZMod 2] V12} (hU : U ∈ stabIn M0 w0) :
    U ∈ Subgroup.centralizer {x0} := by
  obtain ⟨hM, hw⟩ := mem_stabIn.1 hU
  have hiso := f0_gammaU (M0_le_gammaU hM)
  rw [Subgroup.mem_centralizer_iff]
  rintro _ rfl
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, x0_formula, x0_formula, map_add, map_add,
    map_smul, map_smul, hw]
  have h0 : f0 (U v) w0 = f0 v w0 := by
    conv_lhs => rw [← hw]
    exact hiso _ _
  rw [h0]
  rcases g_theta_w0 hU with h | h
  · have h1 : f0 (U v) (theta0 w0) = f0 v (theta0 w0) := by
      conv_lhs => rw [← h]
      exact hiso _ _
    rw [h1, h]
  · have e : theta0 w0 = U (theta0 w0 + w0) := by
      rw [map_add, h, hw, theta0_theta0_add, add_comm w0, add_assoc, add_self_V12, add_zero]
    have h1 : f0 (U v) (theta0 w0) = f0 v (theta0 w0) + f0 v w0 := by
      conv_lhs => rw [e]
      rw [hiso, f0_add_right']
    rw [h1, h, theta0_theta0_add]
    simp only [add_smul, smul_add]
    abel

theorem omegaE_mem_C : omegaE ∈ M0 ⊓ Subgroup.centralizer {x0} := by
  refine ⟨E0_le_M0 omegaE_mem_E0, Subgroup.mem_centralizer_iff.2 ?_⟩
  rintro _ rfl
  exact x0_comm_omegaE

theorem orbit_C_w0 : MulAction.orbit ↥(M0 ⊓ Subgroup.centralizer {x0}) w0 =
    {w0, theta0 w0, theta0 (theta0 w0)} := by
  ext x
  constructor
  · rintro ⟨⟨U, hM, hC⟩, rfl⟩
    change U w0 ∈ ({w0, theta0 w0, theta0 (theta0 w0)} : Set V12)
    have hc : x0 * U = U * x0 := Subgroup.mem_centralizer_iff.1 hC x0 rfl
    obtain ⟨v, hv⟩ := exists_x0_sub_self w0_mem_W0
    have hW : U w0 ∈ W0 := by
      rw [← hv, map_sub, ← LinearEquiv.mul_apply, ← hc, LinearEquiv.mul_apply]
      exact x0_sub_self_mem_W0 _
    have hne : U w0 ≠ 0 := (LinearEquiv.map_ne_zero_iff U).2 fun h => by
      have := congrArg codeOf h
      rw [w0, codeOf_vecOf (by norm_num)] at this
      exact absurd this (by decide)
    rw [mem_W0_iff] at hW
    rw [← vecOf_codeOf (U w0)]
    rcases hW with h | h | h | h <;> rw [h]
    · exact absurd (codeOf_eq_zero h) hne
    · exact Or.inr (Or.inl theta0_w0.symm)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr theta0_theta0_w0.symm)
  · rintro (rfl | rfl | rfl)
    · exact ⟨1, rfl⟩
    · exact ⟨⟨omegaE, omegaE_mem_C⟩, omegaE_apply w0⟩
    · refine ⟨⟨omegaE * omegaE, mul_mem omegaE_mem_C omegaE_mem_C⟩, ?_⟩
      change (omegaE * omegaE) w0 = _
      rw [LinearEquiv.mul_apply, omegaE_apply, omegaE_apply]

theorem ncard_w0_triple : ({w0, theta0 w0, theta0 (theta0 w0)} : Set V12).ncard = 3 := by
  rw [theta0_theta0_w0, theta0_w0, w0]
  refine Set.ncard_eq_three.2 ⟨_, _, _, ?_, ?_, ?_, rfl⟩ <;>
    exact fun h => absurd (vecOf_inj (by norm_num) (by norm_num) h) (by norm_num)

theorem card_centralizer_s12e :
    Nat.card ↥(M0 ⊓ Subgroup.centralizer ({s12e} : Set (V12 ≃ₗ[ZMod 2] V12))) = 311040 := by
  have hst : stabIn (M0 ⊓ Subgroup.centralizer {x0}) w0 = stabIn M0 w0 :=
    le_antisymm (inf_le_inf_right _ inf_le_left) fun U hU =>
      ⟨⟨(mem_stabIn.1 hU).1, stabIn_M0_w0_le hU⟩, (mem_stabIn.1 hU).2⟩
  have h := card_stabIn_mul_ncard orbit_C_w0
  rw [ncard_w0_triple, hst, card_stabIn_M0_w0] at h
  exact h.symm

end CFSG.KD.IF4X

end
