module

public import CFSG.Sporadic.HeldB.AutModel

public noncomputable section

namespace CFSG.KD.He7030.OuterU

open CFSG.Sporadic.HeldB
open CFSG.Sporadic.He (J)

def xiUP : MulAut heP :=
  heConjR (⟨heAutU, heAutU_mem_heAutGroup⟩ : heAutGroup)

def phiU :
    MulAut J ≃* MulAut heP :=
  MulAut.congr (G := J) (H := heP) heJEquivP

def xiU :
    MulAut J :=
  (phiU).symm xiUP

theorem pinv (σ : Equiv.Perm (Fin 8330)) (x : Fin 8330) : σ (σ⁻¹ x) = x :=
  σ.apply_symm_apply x

theorem smul_lift {G : Type} [Monoid G] [MulAction G (Fin 8330)] (π : Equiv.Perm (Fin 8330))
    (z : G) (y : Equiv.Perm (Fin 8330)) (j : Fin 8330) (h : ∀ i, y i = π⁻¹ (z • π i)) :
    z • j = π (y (π⁻¹ j)) := by
  have h1 := h (π⁻¹ j)
  rw [pinv] at h1
  calc z • j = π (π⁻¹ (z • j)) := (pinv π _).symm
    _ = π (y (π⁻¹ j)) := by rw [h1]


theorem congr_apply' (ψ : MulAut J) (x : J) :
    (phiU ψ) (heJEquivP x) = heJEquivP (ψ x) := by
  simp [phiU, MulAut.congr_apply]

theorem xiU_spec (g : J) : heJEquivP (xiU g) = xiUP (heJEquivP g) := by
  have h := congr_apply' xiU g
  rw [xiU, MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem toP_xiU (g : J) : heJToP (xiU g) = heAutU * heJToP g * heAutU⁻¹ := by
  rw [← heJEquivP_apply, xiU_spec, xiUP, heConjR_apply, heJEquivP_apply]
  rfl

theorem xiU_smul (g : J) (j : Fin 8330) :
    xiU g • j = heBridgePerm (heAutU (heBridgePerm⁻¹
      (g • heBridgePerm (heAutU⁻¹ (heBridgePerm⁻¹ j))))) := by
  rw [smul_lift heBridgePerm (xiU g) _ j fun i => heJToP_apply _ i, toP_xiU,
    Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, heJToP_apply]

theorem hOutU
    (f : MulAut J) :
    (∃ k : J, ∀ x, f x = k * x * k⁻¹) ∨ (∃ k : J, ∀ x, f x = k * xiU x * k⁻¹) := by
  obtain ⟨hbij, -⟩ := ctbh_full_automorphism_permutation_model
  obtain ⟨g, hg⟩ := hbij.2 (phiU f)
  rcases mem_heAutGroup_cases g.2 with hgP | hgu
  · left
    refine ⟨heJEquivP.symm ⟨(g : Equiv.Perm (Fin 8330)), hgP⟩, fun x => ?_⟩
    apply heJEquivP.injective
    have h1 := congr_apply' f x
    rw [← h1, ← hg, map_mul, map_mul, MulEquiv.apply_symm_apply, map_inv, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [heConjR_apply]
    rfl
  · right
    set q : Equiv.Perm (Fin 8330) := (g : Equiv.Perm (Fin 8330)) * heAutU with hq
    have hqΓ : q ∈ heAutGroup := heP_le_heAutGroup hgu
    have hgq : (g : Equiv.Perm (Fin 8330)) = q * heAutU := by
      rw [hq, mul_assoc, ← sq, heAutU_sq, mul_one]
    have hgeq : g = ⟨q, hqΓ⟩ * ⟨heAutU, heAutU_mem_heAutGroup⟩ := Subtype.ext hgq
    have hF : phiU f = heConjR ⟨q, hqΓ⟩ * xiUP := by
      rw [← hg, hgeq, map_mul]
      rfl
    refine ⟨heJEquivP.symm ⟨q, hgu⟩, fun x => ?_⟩
    apply heJEquivP.injective
    have h1 := congr_apply' f x
    rw [← h1, hF, map_mul, map_mul, MulEquiv.apply_symm_apply, map_inv,
      MulEquiv.apply_symm_apply, xiU_spec]
    apply Subtype.ext
    simp [heConjR_apply]

end CFSG.KD.He7030.OuterU

end
