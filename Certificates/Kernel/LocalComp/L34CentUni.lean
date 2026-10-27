module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
import TauCeti.RepresentationTheory.CharacterTable.Solvable

public section

namespace CertificateChecks.KernelLC.L34CentUni

open Subgroup CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native

theorem ncard_conj_mul_card {G : Type*} [Group G] (K : Subgroup G) (g : G) :
    {y : G | ∃ k ∈ K, y = k * g * k⁻¹}.ncard * Nat.card ↥(centralizer ({g} : Set G) ⊓ K) =
      Nat.card K := by
  have horb : MulAction.orbit (K.map (MulAut.conj (G := G))) g =
      {y | ∃ k ∈ K, y = k * g * k⁻¹} := by
    ext y
    simp only [MulAction.mem_orbit_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨a, ha⟩, rfl⟩
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 ha
      exact ⟨k, hk, by simp [Subgroup.smul_def]⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨MulAut.conj k, Subgroup.mem_map_of_mem _ hk⟩, by simp [Subgroup.smul_def]⟩
  have hidx : (centralizer ({g} : Set G)).relIndex K =
      (MulAction.stabilizer (K.map (MulAut.conj (G := G))) g).index := by
    rw [← MulAction.stabilizer_comap_conj_eq_centralizer_singleton, Subgroup.relIndex_comap,
      Subgroup.relIndex, MulAction.stabilizer_subgroupOf]
  rw [← horb, ← MulAction.index_stabilizer, ← hidx]
  exact Subgroup.relIndex_mul_card _ _

theorem ncard_conj_R (x : R) :
    {y : Equiv.Perm (Fin 42) | ∃ k ∈ R, y = k * (x : Equiv.Perm (Fin 42)) * k⁻¹}.ncard =
      Nat.card (ConjClasses.mk x).carrier := by
  have h : {y : Equiv.Perm (Fin 42) | ∃ k ∈ R, y = k * (x : Equiv.Perm (Fin 42)) * k⁻¹} =
      Subtype.val '' (ConjClasses.mk x).carrier := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image, ConjClasses.mem_carrier_iff_mk_eq,
      ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨⟨k * x * k⁻¹, R.mul_mem (R.mul_mem hk x.2) (R.inv_mem hk)⟩,
        ⟨⟨k⁻¹, R.inv_mem hk⟩, Subtype.ext ?_⟩, rfl⟩
      simp [mul_assoc]
    · rintro ⟨z, ⟨c, hc⟩, rfl⟩
      refine ⟨(c : Equiv.Perm (Fin 42))⁻¹, R.inv_mem c.2, ?_⟩
      have := congrArg (fun w : R => (w : Equiv.Perm (Fin 42))) hc
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      rw [← this]
      group
  rw [h, Set.ncard_image_of_injective _ Subtype.val_injective, Nat.card_coe_set_eq]

theorem card_cent_r₄ :
    Nat.card ↥(centralizer ({r₄} : Set (Equiv.Perm (Fin 42))) ⊓ R) = 864 := by
  have h := ncard_conj_mul_card R r₄
  have h1 := ncard_conj_R r₄R
  rw [show (r₄R : Equiv.Perm (Fin 42)) = r₄ from rfl, conjClass₄.2] at h1
  rw [h1, card_R] at h
  omega

theorem cent_r₄_facts :
    Nat.card ↥(centralizer ({r₄} : Set (Equiv.Perm (Fin 42))) ⊓ R) = 864 ∧
      Group.IsSolvable ↥(centralizer ({r₄} : Set (Equiv.Perm (Fin 42))) ⊓ R) := by
  have hc := card_cent_r₄
  refine ⟨hc, ?_⟩
  have : Finite ↥(centralizer ({r₄} : Set (Equiv.Perm (Fin 42))) ⊓ R) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  refine TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow Nat.prime_two Nat.prime_three
    (a := 5) (b := 3) ?_
  rw [hc]
  norm_num

end CertificateChecks.KernelLC.L34CentUni

end
