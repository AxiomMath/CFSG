module

public import Certificates.Kernel.StdOdd.Cent7.Theory

public section

namespace CFSG.KD.StdOdd.Cent7

theorem centFacts_of_invClass {G : Type*} [Group G] [Finite G] {s : G} {n a : ℕ}
    (hs7 : orderOf s = 7) (hC : Nat.card (Subgroup.centralizer ({s} : Set G)) = 2 ^ a * (7 * n))
    (hodd : Odd n) {K : Subgroup G} (hK : K ≤ Subgroup.centralizer ({s} : Set G))
    (h : ∃ t ∈ K, t ^ 2 = 1 ∧ t ≠ 1 ∧
      n ≤ {u | ∃ g ∈ K, g * t * g⁻¹ = u}.ncard ∧
      (∃ Q : Subgroup G, Q ≤ K ∧ Q ≤ Subgroup.centralizer {t} ∧ Nat.card Q = 2 ^ a ∧
        ∀ q ∈ Q, q ^ 2 = 1 → q ≠ 1 → ∃ g ∈ K, g * t * g⁻¹ = q) ∧
      ∃ g₁ ∈ K, ∃ g₂ ∈ K, orderOf (t * (g₁ * t * g₁⁻¹) * (g₂ * t * g₂⁻¹)) = 7) :
    (∀ r ∈ Subgroup.centralizer ({s} : Set G), orderOf r ≠ 6) ∧
      ∀ N : Subgroup G, N ≤ Subgroup.centralizer ({s} : Set G) →
        (∀ c ∈ Subgroup.centralizer ({s} : Set G), ∀ x ∈ N, c * x * c⁻¹ ∈ N) →
        Nat.Coprime 7 (Nat.card N) → N = ⊥ := by
  obtain ⟨t, htK, ht2, ht1, hn, ⟨Q, hQK, hQt, hQ, hinv⟩, g₁, hg₁, g₂, hg₂, h7⟩ := h
  set C := Subgroup.centralizer ({s} : Set G) with hCdef
  have hsC : s ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  let s' : C := ⟨s, hsC⟩
  let t' : C := ⟨t, hK htK⟩
  have hcoe : ∀ x : C, orderOf (x : G) = orderOf x := fun x => Subgroup.orderOf_coe x
  have hs' : ∀ g : C, s' * g = g * s' := by
    intro g
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_singleton_iff.1 g.2).symm
  have hs7' : orderOf s' = 7 := by rw [← hcoe]; exact hs7
  have ht2' : t' ^ 2 = 1 := Subtype.ext (by simpa using ht2)
  have ht1' : t' ≠ 1 := fun e => ht1 (congrArg Subtype.val e)
  have hconjK : ∀ {g u : G}, g ∈ K → g * t * g⁻¹ = u →
      ∃ hu : u ∈ C, IsConj t' ⟨u, hu⟩ := by
    rintro g u hg rfl
    refine ⟨C.mul_mem (C.mul_mem (hK hg) (hK htK)) (C.inv_mem (hK hg)), ?_⟩
    exact isConj_iff.2 ⟨⟨g, hK hg⟩, rfl⟩
  have hn' : n ≤ (conjugatesOf t').ncard := by
    refine hn.trans ?_
    have hsub : {u | ∃ g ∈ K, g * t * g⁻¹ = u} ⊆ Subtype.val '' conjugatesOf t' := by
      rintro u ⟨g, hg, hgu⟩
      obtain ⟨hu, hc⟩ := hconjK hg hgu
      exact ⟨⟨u, hu⟩, hc, rfl⟩
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
      (Set.ncard_image_le (Set.toFinite _))
  let Q' : Subgroup C := Q.subgroupOf C
  have hQC : Q ≤ C := hQK.trans hK
  have hQ' : Nat.card Q' = 2 ^ a := by
    rw [← hQ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv
  have hQt' : Q' ≤ Subgroup.centralizer {t'} := by
    intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 (hQt hq)
  have hinv' : ∀ q ∈ Q', q ^ 2 = 1 → q ≠ 1 → IsConj t' q := by
    intro q hq hq2 hq1
    obtain ⟨g, hg, hgq⟩ := hinv q hq (by simpa using congrArg Subtype.val hq2)
      (fun e => hq1 (Subtype.ext e))
    obtain ⟨hu, hc⟩ := hconjK hg hgq
    exact hc
  obtain ⟨h1C, h1⟩ := hconjK hg₁ rfl
  obtain ⟨h2C, h2⟩ := hconjK hg₂ rfl
  have h7' : orderOf (t' * ⟨g₁ * t * g₁⁻¹, h1C⟩ * ⟨g₂ * t * g₂⁻¹, h2C⟩) = 7 := by
    rw [← hcoe]
    exact h7
  have hcard : Nat.card C = 2 ^ a * (7 * n) := hC
  obtain ⟨hno6, hnorm⟩ := invClass_core hs' hs7' ht2' ht1' hn' hQt' hQ' hcard hodd hinv' h1 h2 h7'
  refine ⟨fun r hr => ?_, fun N hNC hNn h7N => ?_⟩
  · have := hno6 ⟨r, hr⟩
    rwa [← hcoe] at this
  · let N' : Subgroup C := N.subgroupOf C
    have hN' : N'.Normal := ⟨fun x hx c => hNn c c.2 x hx⟩
    have hcN : Nat.card N' = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv
    have hbot := hnorm N' hN' (by rw [hcN]; exact h7N)
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hNC hx⟩ : C) ∈ N' := hx
    rw [hbot, Subgroup.mem_bot] at hx'
    exact congrArg Subtype.val hx'

end CFSG.KD.StdOdd.Cent7

end
