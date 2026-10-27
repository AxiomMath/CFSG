module

public import Certificates.Kernel.Schur.Basic
public import CFSG.LieType.Multipliers.CoverWords

public section

namespace CertificateChecks.KernelSchur

open CFSG.Certificates CFSG.Certificates.KB
open scoped commutatorElement

variable {E : Type*} [Group E]

theorem sword_map {F : Type*} [Group F] (f : E →* F) (gen : ℕ → E) (w : List (ℕ × Bool)) :
    sword (fun i => f (gen i)) w = f (sword gen w) := by
  induction w with
  | nil => simp [sword]
  | cons x w ih =>
    rw [sword_cons, sword_cons, ih, map_mul]
    cases x.2 <;> simp

theorem sword_congr {gen gen' : ℕ → E} {w : List (ℕ × Bool)}
    (h : ∀ x ∈ w, gen x.1 = gen' x.1) : sword gen w = sword gen' w := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [sword_cons, sword_cons, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem sword_mem_closure (gen : ℕ → E) {m : ℕ} (w : List (ℕ × Bool)) (hw : ∀ x ∈ w, x.1 < m) :
    sword gen w ∈ Subgroup.closure (gen '' {i | i < m}) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons x w ih =>
    rw [sword_cons]
    have hx : gen x.1 ∈ Subgroup.closure (gen '' {i | i < m}) :=
      Subgroup.subset_closure ⟨x.1, hw x List.mem_cons_self, rfl⟩
    refine Subgroup.mul_mem _ ?_ (ih fun y hy => hw y (List.mem_cons_of_mem _ hy))
    split_ifs
    · exact hx
    · exact Subgroup.inv_mem _ hx

@[expose] def IsSign (z g : E) : Prop := g = 1 ∨ g = z

theorem mem_zpowers_iff_sign {z g : E} (hz2 : z * z = 1) :
    g ∈ Subgroup.zpowers z ↔ IsSign z g := by
  constructor
  · rintro ⟨k, rfl⟩
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m := ⟨k / 2, by omega⟩
      simp only [zpow_mul, zpow_ofNat, pow_two, hz2, one_zpow]
    · right
      obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
      simp only [zpow_add, zpow_mul, zpow_ofNat, pow_two, hz2, one_zpow, one_mul, pow_one]
  · rintro (h | h) <;> rw [h]
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers z

theorem zpowers_normal {z : E} (hz : ∀ g, z * g = g * z) : (Subgroup.zpowers z).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := hn
  have hc : Commute g (z ^ k) := (Commute.zpow_left (hz g) k).symm
  rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  exact Subgroup.zpow_mem_zpowers z k

theorem sign_comm {z s : E} (hz : ∀ g, z * g = g * z) (hs : IsSign z s) (g : E) :
    s * g = g * s := by
  rcases hs with h | h <;> rw [h]
  · simp
  · exact hz g

theorem mem_of_cube {z : E} (hz : ∀ g, z * g = g * z) (hz2 : z * z = 1) {S : Subgroup E}
    {v : E} (hv : v ∈ S ⊔ Subgroup.zpowers z) (h3 : v ^ 3 = 1) : v ∈ S := by
  have : (Subgroup.zpowers z).Normal := zpowers_normal hz
  have hv' : v ∈ ((S ⊔ Subgroup.zpowers z : Subgroup E) : Set E) := hv
  rw [Subgroup.mul_normal] at hv'
  obtain ⟨s, hs, t, ht, rfl⟩ := hv'
  rcases (mem_zpowers_iff_sign hz2).mp ht with h | h <;> rw [h] at h3 ⊢
  · simpa using hs
  · have hc : Commute s z := (hz s).symm
    rw [hc.mul_pow, show z ^ 3 = z by rw [pow_succ, pow_two, hz2, one_mul]] at h3
    have hz' : z = (s ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right h3
    exact S.mul_mem hs (hz' ▸ S.inv_mem (S.pow_mem hs 3))

@[expose] def Cen (k : E) : Prop := ∀ g, k * g = g * k

theorem cen_mul {k k' : E} (hk : Cen k) (hk' : Cen k') : Cen (k * k') := by
  intro g
  rw [mul_assoc, hk' g, ← mul_assoc, hk g, mul_assoc]

theorem cen_inv {k : E} (hk : Cen k) : Cen k⁻¹ := by
  intro g
  have h := hk g⁻¹
  calc k⁻¹ * g = (g⁻¹ * k)⁻¹ := by group
    _ = (k * g⁻¹)⁻¹ := by rw [h]
    _ = g * k⁻¹ := by group

theorem comm_mul_cen_left (x y : E) {k : E} (hk : Cen k) : ⁅x * k, y⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc x * k * y * (x * k)⁻¹ * y⁻¹ = x * (k * y) * k⁻¹ * x⁻¹ * y⁻¹ := by group
    _ = x * (y * k) * k⁻¹ * x⁻¹ * y⁻¹ := by rw [hk y]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem comm_mul_cen_right (x y : E) {k : E} (hk : Cen k) : ⁅x, y * k⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc x * (y * k) * x⁻¹ * (y * k)⁻¹ = x * y * (k * x⁻¹) * k⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * k) * k⁻¹ * y⁻¹ := by rw [hk x⁻¹]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem lift_central {ι : Type*} {g h c : ι → E} (hc : ∀ i, Cen (c i))
    (hg : ∀ i, g i = h i * c i) (w : FreeGroup ι) :
    ∃ k, Cen k ∧ FreeGroup.lift g w = FreeGroup.lift h w * k := by
  induction w using FreeGroup.induction_on with
  | one => exact ⟨1, fun x => by simp, by simp⟩
  | of i => exact ⟨c i, hc i, by simp [hg i]⟩
  | inv_of i ih =>
    obtain ⟨k, hk, e⟩ := ih
    refine ⟨k⁻¹, cen_inv hk, ?_⟩
    rw [map_inv, map_inv, e, mul_inv_rev, (cen_inv hk) _]
  | mul x y ihx ihy =>
    obtain ⟨k, hk, ex⟩ := ihx
    obtain ⟨k', hk', ey⟩ := ihy
    refine ⟨k * k', cen_mul hk hk', ?_⟩
    rw [map_mul, map_mul, ex, ey, mul_assoc, ← mul_assoc k, hk, mul_assoc, mul_assoc]

theorem lift_commWords {m : ℕ} (f : Fin m → E)
    (c : List (List (Fin m × Bool) × List (Fin m × Bool))) :
    FreeGroup.lift f (FreeGroup.mk (CFSG.LieType.Multipliers.commWords c)) =
      (c.map fun p => ⁅FreeGroup.lift f (FreeGroup.mk p.1), FreeGroup.lift f (FreeGroup.mk p.2)⁆).prod := by
  induction c with
  | nil => rfl
  | cons p c ih =>
    rw [List.map_cons, List.prod_cons, ← ih]
    have e : CFSG.LieType.Multipliers.commWords (p :: c) =
        CFSG.LieType.Multipliers.commWord p.1 p.2 ++ CFSG.LieType.Multipliers.commWords c := by
      simp [CFSG.LieType.Multipliers.commWords]
    rw [e, ← FreeGroup.mul_mk, map_mul, CFSG.LieType.Multipliers.mk_commWord, map_commutatorElement]

theorem lift_commWords_central {m : ℕ} {g h c : Fin m → E} (hc : ∀ i, Cen (c i))
    (hg : ∀ i, g i = h i * c i) (cs : List (List (Fin m × Bool) × List (Fin m × Bool))) :
    FreeGroup.lift g (FreeGroup.mk (CFSG.LieType.Multipliers.commWords cs)) =
      FreeGroup.lift h (FreeGroup.mk (CFSG.LieType.Multipliers.commWords cs)) := by
  rw [lift_commWords, lift_commWords]
  congr 1
  apply List.map_congr_left
  intro p _
  obtain ⟨k, hk, e⟩ := lift_central hc hg (FreeGroup.mk p.1)
  obtain ⟨k', hk', e'⟩ := lift_central hc hg (FreeGroup.mk p.2)
  rw [e, e', comm_mul_cen_left _ _ hk, comm_mul_cen_right _ _ hk']

end CertificateChecks.KernelSchur

end
