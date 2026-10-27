module

public import CFSG.GH74.Generic.S45.LEvSporSpec

public section

namespace CertificateChecks.KernelGH74

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem conj_mem_closure {T : Set G} {e : G} (h : ∀ t ∈ T, e * t * e⁻¹ ∈ closure T) :
    ∀ m ∈ closure T, e * m * e⁻¹ ∈ closure T := by
  intro m hm
  have : closure T ≤ (closure T).comap (MulAut.conj e).toMonoidHom :=
    (closure_le _).2 fun t ht => h t ht
  exact this hm

theorem conj_mem_of_normalizer {M : Subgroup G} {y m : G} (hy : y ∈ normalizer (M : Set G))
    (hm : m ∈ M) : y * m * y⁻¹ ∈ M :=
  (mem_normalizer_iff.1 hy m).1 hm

theorem comm_mem_of_gens [Finite G] {S : Set G} {M : Subgroup G}
    (hn : ∀ s ∈ S, ∀ m ∈ M, s * m * s⁻¹ ∈ M) (hc : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ ∈ M) :
    ∀ x ∈ closure S, ∀ y ∈ closure S, ⁅x, y⁆ ∈ M := by
  have hN : closure S ≤ normalizer (M : Set G) :=
    (closure_le _).2 fun s hs =>
    CFSG.GH74.Generic.S45.EvSpor.mem_normalizer_of_conj_le (hn s hs)
  have key1 : ∀ s ∈ S, ∀ y ∈ closure S, ⁅s, y⁆ ∈ M := by
    intro s hs y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact hc s hs y hy
    | one => simp [commutatorElement_def]
    | mul y z hy hz ihy ihz =>
      have e : ⁅s, y * z⁆ = ⁅s, y⁆ * (y * ⁅s, z⁆ * y⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact M.mul_mem ihy (conj_mem_of_normalizer (hN hy) ihz)
    | inv y hy ihy =>
      have e : ⁅s, y⁻¹⁆ = y⁻¹ * ⁅s, y⁆⁻¹ * y⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact conj_mem_of_normalizer ((normalizer (M : Set G)).inv_mem (hN hy)) (M.inv_mem ihy)
  intro x hx y hy
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact key1 x hx y hy
  | one => simp [commutatorElement_def]
  | mul x z hx hz ihx ihz =>
    have e : ⁅x * z, y⁆ = x * ⁅z, y⁆ * x⁻¹ * ⁅x, y⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact M.mul_mem (conj_mem_of_normalizer (hN hx) ihz) ihx
  | inv x hx ihx =>
    have e : ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact conj_mem_of_normalizer ((normalizer (M : Set G)).inv_mem (hN hx)) (M.inv_mem ihx)

end CertificateChecks.KernelGH74

end
