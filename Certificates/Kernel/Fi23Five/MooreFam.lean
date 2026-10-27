module

public import CFSG.Sporadic.Fi23.Pair
public import CFSG.Sporadic.SchreierLemmas.MooreChain

public section

namespace Fi23Moore10137

open CFSG.Sporadic.Fi23 CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm
  CFSG.Perm.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem cube_of_ord {G : Type*} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (ho : orderOf (x * y) = 1 ∨ orderOf (x * y) = 2 ∨ orderOf (x * y) = 3)
    (hne : x * y ≠ y * x) : (x * y) ^ 3 = 1 := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  rcases ho with h | h | h
  · have e : y = x := by rw [eq_inv_of_mul_eq_one_right (orderOf_eq_one_iff.1 h), hxi]
    rw [e] at hne
    exact absurd rfl hne
  · have h2 := pow_orderOf_eq_one (x * y)
    rw [h, pow_two] at h2
    have e := eq_inv_of_mul_eq_one_left h2
    rw [mul_inv_rev, hxi, hyi] at e
    exact absurd e hne
  · rw [← h]
    exact pow_orderOf_eq_one _

theorem mul_ne_one_of_ne_comm {G : Type*} [Group G] {x y : G} (hx : x * x = 1)
    (hne : x * y ≠ y * x) : x * y ≠ 1 := by
  intro h
  have e : y = x := by rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hx]
  rw [e] at hne
  exact hne rfl


theorem sq_D : ∀ x ∈ {x : J | IsConj d x}, x * x = 1 := fun x hx => by
  rw [Set.mem_setOf_eq] at hx
  have h := pow_orderOf_eq_one x
  rw [orderOf_of_isConj hx, pow_two] at h
  exact h

theorem cube_D : ∀ x ∈ {x : J | IsConj d x}, ∀ y ∈ {x : J | IsConj d x}, x * y ≠ y * x →
    (x * y) ^ 3 = 1 := fun x hx y hy hne =>
  cube_of_ord (G := J) (sq_D x hx) (sq_D y hy) (orderOf_mul_of_isConj hx hy) hne

theorem moore_fam (s : ℕ → J) (hD : ∀ i < 6, IsConj d (s i))
    (hnc : ∀ i, i + 1 < 6 → s i * s (i + 1) ≠ s (i + 1) * s i)
    (hc : ∀ i j, i + 2 ≤ j → j < 6 → s i * s j = s j * s i) :
    CFSG.Sporadic.SchreierLemmas.IsMooreFamily (6 - 1)
      (CFSG.Sporadic.SchreierLemmas.mooreOfChain s) ∧ s 0 * s 1 ≠ 1 := by
  refine ⟨CFSG.Sporadic.SchreierLemmas.moore_of_chain (G := J) (D := {x : J | IsConj d x})
    ?_ ?_ ?_ (by norm_num) s hD hnc hc,
    mul_ne_one_of_ne_comm (G := J) (sq_D _ (hD 0 (by norm_num))) (hnc 0 (by norm_num))⟩
  · exact sq_D
  · exact cube_D
  · exact fun _ hx y _ => hx.trans (isConj_iff.2 ⟨y, rfl⟩)

end Fi23Moore10137
