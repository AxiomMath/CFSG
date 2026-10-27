module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.U62CoversLarge

public section

namespace CertificateChecks.U62Group

open Subgroup CFSG.EvenSporadicStandard.Induction.Fi

variable {G : Type*} [Group G]

theorem le_of_index_two {S : Set G} {H K : Subgroup G} (t : G)
    (h2 : ∀ g ∈ closure S, ∀ h ∈ closure S, g ∉ H → h ∉ H → g * h ∈ H)
    (hin : ∀ s ∈ S, s ∈ H → s ∈ K ∧ t * s * t⁻¹ ∈ K)
    (hout : ∀ s ∈ S, s ∉ H → s * t⁻¹ ∈ K ∧ t * s ∈ K) :
    ∀ g ∈ closure S, g ∈ H → g ∈ K := by
  suffices P : ∀ g ∈ closure S, (g ∈ H → g ∈ K ∧ t * g * t⁻¹ ∈ K) ∧
      (g ∉ H → g * t⁻¹ ∈ K ∧ t * g ∈ K) from fun g hg hH => ((P g hg).1 hH).1
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact ⟨hin s hs, hout s hs⟩
  | one => exact ⟨fun _ => ⟨K.one_mem, by rw [mul_one, mul_inv_cancel]; exact K.one_mem⟩,
      fun h => absurd H.one_mem h⟩
  | mul a b ha hb iha ihb =>
    refine ⟨fun hab => ?_, fun hab => ?_⟩
    · by_cases haH : a ∈ H
      · have hbH : b ∈ H := by
          have := H.mul_mem (H.inv_mem haH) hab
          rwa [inv_mul_cancel_left] at this
        obtain ⟨k1, k2⟩ := iha.1 haH
        obtain ⟨k3, k4⟩ := ihb.1 hbH
        refine ⟨K.mul_mem k1 k3, ?_⟩
        have := K.mul_mem k2 k4
        rwa [show t * a * t⁻¹ * (t * b * t⁻¹) = t * (a * b) * t⁻¹ by group] at this
      · have hbH : b ∉ H := fun hbH => haH (by
          have := H.mul_mem hab (H.inv_mem hbH)
          rwa [mul_inv_cancel_right] at this)
        obtain ⟨k1, k2⟩ := iha.2 haH
        obtain ⟨k3, k4⟩ := ihb.2 hbH
        constructor
        · have := K.mul_mem k1 k4
          rwa [show a * t⁻¹ * (t * b) = a * b by group] at this
        · have := K.mul_mem k2 k3
          rwa [show t * a * (b * t⁻¹) = t * (a * b) * t⁻¹ by group] at this
    · by_cases haH : a ∈ H
      · have hbH : b ∉ H := fun hbH => hab (H.mul_mem haH hbH)
        obtain ⟨k1, k2⟩ := iha.1 haH
        obtain ⟨k3, k4⟩ := ihb.2 hbH
        constructor
        · have := K.mul_mem k1 k3
          rwa [show a * (b * t⁻¹) = a * b * t⁻¹ by group] at this
        · have := K.mul_mem k2 k4
          rwa [show t * a * t⁻¹ * (t * b) = t * (a * b) by group] at this
      · have hbH : b ∈ H := by
          by_contra hbH
          exact hab (h2 a ha b hb haH hbH)
        obtain ⟨k1, k2⟩ := iha.2 haH
        obtain ⟨k3, k4⟩ := ihb.1 hbH
        constructor
        · have := K.mul_mem k1 k4
          rwa [show a * t⁻¹ * (t * b * t⁻¹) = a * b * t⁻¹ by group] at this
        · have := K.mul_mem k2 k3
          rwa [show t * a * b = t * (a * b) by group] at this
  | inv a ha iha =>
    refine ⟨fun hab => ?_, fun hab => ?_⟩
    · have haH : a ∈ H := by simpa using H.inv_mem hab
      obtain ⟨k1, k2⟩ := iha.1 haH
      refine ⟨K.inv_mem k1, ?_⟩
      have := K.inv_mem k2
      rwa [show (t * a * t⁻¹)⁻¹ = t * a⁻¹ * t⁻¹ by group] at this
    · have haH : a ∉ H := fun h => hab (H.inv_mem h)
      obtain ⟨k1, k2⟩ := iha.2 haH
      constructor
      · have := K.inv_mem k2
        rwa [show (t * a)⁻¹ = a⁻¹ * t⁻¹ by group] at this
      · have := K.inv_mem k1
        rwa [show (a * t⁻¹)⁻¹ = t * a⁻¹ by group] at this

variable [Finite G]

theorem mul_card_centralizer_le (X : Set G) {m : ℕ} (g : Fin m → G)
    (hg : ∀ s t : Fin m, (∀ x ∈ X, g s * x * (g s)⁻¹ = g t * x * (g t)⁻¹) → s = t) :
    m * Nat.card (centralizer X) ≤ Nat.card G := by
  set C := centralizer X
  have hinj : Function.Injective fun t => (QuotientGroup.mk (g t) : G ⧸ C) := by
    intro s t hst
    apply hg
    intro x hx
    have h := mem_centralizer_iff.1 (QuotientGroup.eq.1 hst) x hx
    calc g s * x * (g s)⁻¹ = g s * (x * ((g s)⁻¹ * g t)) * (g t)⁻¹ := by group
      _ = g s * ((g s)⁻¹ * g t * x) * (g t)⁻¹ := by rw [h]
      _ = g t * x * (g t)⁻¹ := by group
  have hm : m ≤ C.index := by
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin] at this
  calc m * Nat.card C ≤ C.index * Nat.card C := Nat.mul_le_mul_right _ hm
    _ = Nat.card G := by rw [mul_comm]; exact C.card_mul_index

omit [Finite G] in
theorem closure_comm {X : Set G} (hX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    ∀ u ∈ closure X, ∀ v ∈ closure X, u * v = v * u := by
  have h1 : closure X ≤ centralizer X :=
    (closure_le _).2 fun x hx => mem_centralizer_iff.2 fun y hy => hX y hy x hx
  intro u hu v hv
  have h2 : closure X ≤ centralizer {u} :=
    (closure_le _).2 fun x hx => by
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.1 (h1 hu) x hx
  have h3 := h2 hv
  rw [mem_centralizer_singleton_iff] at h3
  exact h3.symm

omit [Finite G] in
theorem closure_sq {X : Set G} (hX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hX2 : ∀ x ∈ X, x * x = 1) : ∀ u ∈ closure X, u * u = 1 := by
  intro u hu
  induction hu using Subgroup.closure_induction with
  | mem x hx => exact hX2 x hx
  | one => exact mul_one 1
  | mul a b ha hb iha ihb =>
    rw [show a * b * (a * b) = a * (b * a) * b by group, ← closure_comm hX a ha b hb,
      show a * (a * b) * b = a * a * (b * b) by group, iha, ihb, one_mul]
  | inv a _ iha => rw [← mul_inv_rev, iha, inv_one]

theorem largeCentralizer_eq (n : ℕ) (E : Subgroup G) (X : Set G)
    (hEl : ∀ x, IsLargeInvAt n x → x ∈ E) (hEc : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u)
    (hXl : ∀ x ∈ X, IsLargeInvAt n x) (hcard : Nat.card (centralizer X) ≤ Nat.card E) :
    largeCentralizer n G = E := by
  have hE : E ≤ largeCentralizer n G := fun u hu =>
    mem_centralizer_iff.2 fun x hx => hEc x (hEl x hx) u hu
  have hX : largeCentralizer n G ≤ centralizer X := centralizer_le fun x hx => hXl x hx
  have hEX : E = centralizer X := Subgroup.eq_of_le_of_card_ge (hE.trans hX) hcard
  refine le_antisymm ?_ hE
  rw [hEX]
  exact hX

end CertificateChecks.U62Group
