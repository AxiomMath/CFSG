module

public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

public section

namespace CertificateChecks.KernelMisc.TitsJT.Grp

open scoped commutatorElement

variable {G : Type*} [Group G] {S : Set G} {z : G}

@[expose] def Z0 (z x : G) : Prop := x = 1 ∨ x = z

theorem z0_one : Z0 z 1 := Or.inl rfl

theorem z0_mul (hz2 : z * z = 1) {a b : G} (ha : Z0 z a) (hb : Z0 z b) : Z0 z (a * b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact Or.inl (mul_one 1)
  · exact Or.inr (one_mul _)
  · exact Or.inr (mul_one _)
  · exact Or.inl hz2

theorem z0_inv (hz2 : z * z = 1) {a : G} (ha : Z0 z a) : Z0 z a⁻¹ := by
  rcases ha with rfl | rfl
  · exact Or.inl inv_one
  · exact Or.inr (inv_eq_of_mul_eq_one_right hz2)

theorem z0_conj (hz : ∀ y ∈ Subgroup.closure S, Commute z y) {a y : G} (ha : Z0 z a)
    (hy : y ∈ Subgroup.closure S) : y * a * y⁻¹ = a := by
  rcases ha with rfl | rfl
  · group
  · rw [(hz y hy).symm.eq]
    group

theorem comm_mul_right (x y w : G) : ⁅x, y * w⁆ = ⁅x, y⁆ * (y * ⁅x, w⁆ * y⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem comm_inv_right (x y : G) : ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y⁻¹⁻¹ := by
  simp only [commutatorElement_def]
  group

theorem comm_mul_left (x x' y : G) : ⁅x * x', y⁆ = x * ⁅x', y⁆ * x⁻¹ * ⁅x, y⁆ := by
  simp only [commutatorElement_def]
  group

theorem comm_inv_left (x y : G) : ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x⁻¹⁻¹ := by
  simp only [commutatorElement_def]
  group

variable (hz : ∀ y ∈ Subgroup.closure S, Commute z y) (hz2 : z * z = 1)
include hz hz2

theorem forall_z0_iff {x : G} :
    (∀ y ∈ Subgroup.closure S, Z0 z ⁅x, y⁆) ↔ ∀ s ∈ S, Z0 z ⁅x, s⁆ := by
  refine ⟨fun h s hs => h s (Subgroup.subset_closure hs), fun h y hy => ?_⟩
  induction hy using Subgroup.closure_induction with
  | mem s hs => exact h s hs
  | one => rw [commutatorElement_one_right]; exact z0_one
  | mul y w hy hw py pw =>
    rw [comm_mul_right, z0_conj hz pw hy]
    exact z0_mul hz2 py pw
  | inv y hy py =>
    rw [comm_inv_right, z0_conj hz (z0_inv hz2 py) (Subgroup.inv_mem _ hy)]
    exact z0_inv hz2 py

@[expose] def eSub (hz : ∀ y ∈ Subgroup.closure S, Commute z y) (hz2 : z * z = 1) : Subgroup G where
  carrier := {x : G | x ∈ Subgroup.closure S ∧ ∀ y ∈ Subgroup.closure S, Z0 z ⁅x, y⁆}
  mul_mem' := by
    rintro x x' ⟨hx, px⟩ ⟨hx', px'⟩
    refine ⟨Subgroup.mul_mem _ hx hx', fun y hy => ?_⟩
    rw [comm_mul_left, z0_conj hz (px' y hy) hx]
    exact z0_mul hz2 (px' y hy) (px y hy)
  one_mem' := ⟨Subgroup.one_mem _, fun y _ => by rw [commutatorElement_one_left]; exact z0_one⟩
  inv_mem' := by
    rintro x ⟨hx, px⟩
    refine ⟨Subgroup.inv_mem _ hx, fun y hy => ?_⟩
    rw [comm_inv_left, z0_conj hz (z0_inv hz2 (px y hy)) (Subgroup.inv_mem _ hx)]
    exact z0_inv hz2 (px y hy)

theorem mem_eSub_iff {x : G} (hx : x ∈ Subgroup.closure S) :
    x ∈ eSub hz hz2 ↔ ∀ s ∈ S, Z0 z ⁅x, s⁆ :=
  ⟨fun h => (forall_z0_iff hz hz2).1 h.2, fun h => ⟨hx, (forall_z0_iff hz hz2).2 h⟩⟩

omit hz hz2 in
theorem commute_of_sq {K : Subgroup G} (h : ∀ e ∈ K, e * e = 1) {e e' : G} (he : e ∈ K)
    (he' : e' ∈ K) : Commute e e' := by
  have h1 := h _ (K.mul_mem he he')
  have a : e⁻¹ = e := inv_eq_of_mul_eq_one_right (h e he)
  have b : e'⁻¹ = e' := inv_eq_of_mul_eq_one_right (h e' he')
  have c : (e * e')⁻¹ = e * e' := inv_eq_of_mul_eq_one_right h1
  rw [mul_inv_rev, a, b] at c
  exact c.symm

theorem comm_mul_iff (hz1 : z ≠ 1) {b x y : G} (hb : b ∈ eSub hz hz2)
    (hx : x ∈ Subgroup.closure S) (hy : y ∈ Subgroup.closure S) :
    Commute b (x * y) ↔ (Commute b x ↔ Commute b y) := by
  rw [← commutatorElement_eq_one_iff_commute, ← commutatorElement_eq_one_iff_commute,
    ← commutatorElement_eq_one_iff_commute, comm_mul_right, z0_conj hz (hb.2 y hy) hx]
  rcases hb.2 x hx with h1 | h1 <;> rcases hb.2 y hy with h2 | h2 <;> rw [h1, h2]
  · simp
  · simp [hz1]
  · simp [hz1]
  · simp [hz2, hz1]

end CertificateChecks.KernelMisc.TitsJT.Grp

end
