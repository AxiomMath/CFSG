module

public import Certificates.Kernel.IdxFour.Vt
public import Certificates.Kernel.IdxFour.Tcoset

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.KD.IF4T

open CFSG.KC.IF4L CFSG.KD.IF4L CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.IdxFour

theorem comm_omegaE_iff {m : ℕ} (hm : m < 32) :
    subG lbarL m * omegaE = omegaE * subG lbarL m ↔ m = 0 ∨ m ∈ INN := by
  have hθ : thetaU = omegaE := LinearEquiv.ext fun x => by rw [thetaU_apply, omegaE_apply]
  rw [← hθ]
  exact comm_theta_iff hm

theorem mem_INN_of_inner {t : V12 ≃ₗ[ZMod 2] V12} (ht : t ∈ genGrp lbarGens) (h1 : t ≠ 1)
    (h2 : t * omegaE = omegaE * t) : ∃ m ∈ INN, subG lbarL m = t := by
  obtain ⟨m, hm, rfl⟩ := mem_Lbar_iff.1 ht
  refine ⟨m, ((comm_omegaE_iff hm).1 h2).resolve_left fun h0 => h1 ?_, rfl⟩
  rw [h0]
  exact subG_zero _

theorem facts17608 :
    Nat.card (genGrp lbarGens) = 32 ∧
    (∀ l ∈ genGrp lbarGens, l * l = 1) ∧
    (∀ l ∈ genGrp lbarGens, ∀ l' ∈ genGrp lbarGens, l * l' = l' * l) ∧
    (∀ g ∈ genGrp sGens, ∀ l ∈ genGrp lbarGens, g * l * g⁻¹ ∈ genGrp lbarGens) ∧
    Nat.card {t : V12 ≃ₗ[ZMod 2] V12 // t ∈ genGrp lbarGens ∧ t * omegaE = omegaE * t} = 16 ∧
    (∀ t ∈ genGrp lbarGens, ∀ t' ∈ genGrp lbarGens, t ≠ 1 → t' ≠ 1 →
      t * omegaE = omegaE * t → t' * omegaE = omegaE * t' →
      ∃ g ∈ genGrp sGens, g * t * g⁻¹ = t') ∧
    720 ≤ (Subgroup.centralizer
      {t | t ∈ genGrp lbarGens ∧ t * omegaE = omegaE * t}).relIndex (genGrp sGens) ∧
    spanOf vtBasis ≤ Submodule.span (ZMod 2) {y | ∃ l ∈ genGrp lbarGens, ∃ x : V12,
      f0 x (vecOf 15) = 0 ∧ f0 x (vecOf 960) = 0 ∧ y = l x - x} := by
  have hθ : thetaU = omegaE := LinearEquiv.ext fun x => by rw [thetaU_apply, omegaE_apply]
  refine ⟨card_Lbar, fun l hl => Lbar_sq hl, fun l hl l' hl' => Lbar_comm hl hl',
    fun g hg l hl => conj_mem_Lbar hg hl, by rw [← hθ]; exact card_comm_theta, ?_, ?_, vt_le⟩
  · intro t ht t' ht' h1 h1' h2 h2'
    obtain ⟨m, hm, rfl⟩ := mem_INN_of_inner ht h1 h2
    obtain ⟨m', hm', rfl⟩ := mem_INN_of_inner ht' h1' h2'
    exact exists_conj_inn hm hm'
  · refine le_relIndex fun c hc m hm => ?_
    have hmem : subG lbarL m ∈ {t | t ∈ genGrp lbarGens ∧ t * omegaE = omegaE * t} :=
      ⟨subG_mem_Lbar m, (comm_omegaE_iff (by simpa using INN_lt m hm)).2 (Or.inr hm)⟩
    exact (Subgroup.mem_centralizer_iff.1 hc _ hmem).symm

theorem facts17610 : ∀ t ∈ genGrp lbarGens, t ≠ 1 → t * omegaE = omegaE * t →
    ModelInner (spanOf vtBasis) t := by
  have hθ : thetaU = omegaE := LinearEquiv.ext fun x => by rw [thetaU_apply, omegaE_apply]
  intro t ht h1 h2
  exact modelInner_inner ht h1 (by rw [hθ]; exact h2.symm)

end CFSG.KD.IF4T

end
