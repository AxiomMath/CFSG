module

public import Certificates.Kernel.ThFive.Check
public import CFSG.Certificates.Kernel.ThFive.Sound
public import CFSG.Certificates.Kernel.ThFive.PGroup
public import Certificates.Kernel.ThCent.Consumers
public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import CFSG.LocalAnalysis.StandardType.GGSporKRestClassesCl
public import CFSG.LocalAnalysis.StandardType.GGSporKRestClasses
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFive

public section

namespace CFSG.StandardType.SporadicShape

open scoped commutatorElement

theorem sporKRest_isConj_of_cube {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {x y c : G}
    (hx : x ^ p = 1) (hy : y ^ p = 1) (hc : c = x * y * x ^ (p - 1) * y ^ (p - 1))
    (hcx : c * x = x * c) (hcy : c * y = y * c)
    (hinj : ∀ i j k i' j' k' : ℕ, i < p → j < p → k < p → i' < p → j' < p → k' < p →
      x ^ i * y ^ j * c ^ k = x ^ i' * y ^ j' * c ^ k' → i = i' ∧ j = j' ∧ k = k')
    (hfac : (Nat.card G).factorization p = 3)
    (hconj : ∀ i j k : ℕ, i < p → j < p → k < p → i + j + k ≠ 0 →
      ∃ m : G, m * (x ^ i * y ^ j * c ^ k) = c * m)
    {t : G} (ht : IsPGroup p (Subgroup.zpowers t)) (ht1 : t ≠ 1) : IsConj c t := by
  have hp0 : 0 < p := hp.out.pos
  have hxy : ⁅x, y⁆ = c := by
    rw [hc, CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair.commutatorElement_eq_of_pow hp0 hx hy]
  have hzx : Commute ⁅x, y⁆ x := by rw [hxy]; exact hcx
  have hzy : Commute ⁅x, y⁆ y := by rw [hxy]; exact hcy
  have hQ : Nat.card (Subgroup.closure ({x, y} : Set G)) = p ^ (Nat.card G).factorization p := by
    rw [hfac]
    refine CFSG.SectionRank.LocalWitness.card_closure_eq_cube hp0 hx hy hzx hzy ?_
    rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
    simp only [hxy] at h
    obtain ⟨h1, h2, h3⟩ := hinj i j k i' j' k' i.2 j.2 k.2 i'.2 j'.2 k'.2 h
    exact Prod.ext (Fin.ext h1) (Prod.ext (Fin.ext h2) (Fin.ext h3))
  let S₀ : Sylow p G := Sylow.ofCard (Subgroup.closure ({x, y} : Set G)) hQ
  obtain ⟨P, hP⟩ := ht.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P S₀
  have hgt : g * t * g⁻¹ ∈ Subgroup.closure ({x, y} : Set G) := by
    change g * t * g⁻¹ ∈ (S₀ : Subgroup G)
    rw [← hg]
    change g * t * g⁻¹ ∈ (((g • P : Sylow p G) : Set G))
    rw [Sylow.coe_smul, Set.mem_smul_set]
    refine ⟨t, hP (Subgroup.mem_zpowers t), ?_⟩
    change (MulAut.conj g) t = g * t * g⁻¹
    rw [MulAut.conj_apply]
  obtain ⟨i, j, k, hi, hj, hk, hw⟩ :=
    CFSG.SectionRank.LocalWitness.mem_closure_normalForm hp0 hx hy hzx hzy hgt
  rw [hxy] at hw
  have hijk : i + j + k ≠ 0 := by
    intro h0
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    have hk0 : k = 0 := by omega
    rw [hi0, hj0, hk0, pow_zero, pow_zero, pow_zero, mul_one, mul_one] at hw
    apply ht1
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [hw]; group
  obtain ⟨m, hm⟩ := hconj i j k hi hj hk hijk
  rw [← hw] at hm
  refine isConj_iff.2 ⟨(m * g)⁻¹, ?_⟩
  calc (m * g)⁻¹ * c * (m * g)⁻¹⁻¹ = g⁻¹ * (m⁻¹ * (c * m)) * g := by group
    _ = g⁻¹ * (m⁻¹ * (m * (g * t * g⁻¹))) * g := by rw [hm]
    _ = t := by group

section Th

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFiveNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFive
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent

local notation "R5" => slpJ a b prog5

local notation "c5" => R5 94 * R5 105 * R5 94 ^ 4 * R5 105 ^ 4

theorem thFive_isConj_c5
    {t : J}
    (ht : IsPGroup 5 (Subgroup.zpowers t)) (ht1 : t ≠ 1) : IsConj c5 t := by
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine sporKRest_isConj_of_cube (c := c5) thFive_facts.x_pow thFive_facts.y_pow rfl
    thFive_facts.cx thFive_facts.cy thFive_facts.inj ?_ thFive_facts.conj ht ht1
  rw [CFSG.Sporadic.Th.Max3.natCard_J,
    show (90745943887872000 : ℕ) = 5 ^ 3 * 725967551102976 by norm_num,
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair.factorization_pow_mul Nat.prime_five 3 _
      (by norm_num)]

end Th

end CFSG.StandardType.SporadicShape

namespace CertificateChecks.KernelThFive

open CFSG.Sporadic.Th CFSG.KC.ThFive CFSG.KD.ThFive CFSG.StandardType.SporadicShape
open scoped commutatorElement

theorem sporKRest_cover_Th_5_kernel :
    SporKRestCover 5 J := by
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨hA, hB, -, hk⟩ := CertificateChecks.KernelThCent.fwd_mats
  have hchk := chk_sound (P1 := S.P1) (P2 := S.P2) (P3 := S.P3) (O1 := S.O1) (O2 := S.O2) (O3 := S.O3)
    hk a b hA hB chk_ok
  obtain ⟨q₁, q₂, r, g, c₁, z, y₁, y₂, w, hq₁, hq₂, hC₁, hC₂, -, hr1, hry, har, hcr, hrg, hzy, hwb,
    hy₁, hy₂, hw⟩ := hchk
  have hcomm := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair.commutatorElement_eq_of_pow
    (by norm_num) hq₁ hq₂
  have h4 : (5 : ℕ) - 1 = 4 := rfl
  rw [h4] at hcomm
  have hS₀ : IsPGroup 5 (Subgroup.closure ({q₁, q₂} : Set J)) :=
    isPGroup_closure_of_comm (by norm_num) hq₁ hq₂ (by rw [hcomm]; exact hC₁)
      (by rw [hcomm]; exact hC₂)
  have hrS : r ∈ Subgroup.closure ({q₁, q₂} : Set J) := hry ▸ hy₁
  have hr5 : IsPGroup 5 (Subgroup.zpowers r) := hS₀.to_le (Subgroup.zpowers_le.2 hrS)
  let S₀ := Subgroup.closure ({q₁, q₂} : Set J)
  let Z : Set J := {a, c₁, z}
  have hsub : ∀ t ∈ ({q₁, q₂, a, c₁, z} : Set J), t ∈ Subgroup.closure ((S₀ : Set J) ∪ Z) := by
    intro t ht
    apply Subgroup.subset_closure
    rcases ht with rfl | rfl | ht
    · exact Or.inl (Subgroup.subset_closure (by simp))
    · exact Or.inl (Subgroup.subset_closure (by simp))
    · exact Or.inr ht
  refine sporKRest_cover_of_classes Nat.prime_five [r] (fun s hs => ⟨r, List.mem_singleton_self r, ?_⟩)
    fun r' hr' x hx => ?_
  · have hs1 : s ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hs
      norm_num at hs
    have hs5 : IsPGroup 5 (Subgroup.zpowers s) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
    exact ((thFive_isConj_c5 hr5 hr1).symm).trans (thFive_isConj_c5 hs5 hs1)
  rw [List.mem_singleton] at hr'
  subst hr'
  refine sporKRest_generating_of_pgroup_closure Nat.prime_five a b closure_ab S₀ hS₀ r' Z ?_
    (Subgroup.subset_closure (Or.inr (by simp [Z]))) ?_ hx
  · intro t ht
    rcases ht with rfl | rfl | ht
    · exact ⟨1, r', hrS, by group, har⟩
    · exact ⟨1, r', hrS, by group, hcr⟩
    · rw [Set.mem_singleton_iff] at ht
      subst ht
      exact ⟨g, y₂, hy₂, by rw [mul_assoc, hrg, ← mul_assoc, inv_mul_cancel, one_mul], hzy⟩
  · rw [← hwb]
    exact (Subgroup.closure_le _).2 hsub hw

end CertificateChecks.KernelThFive

end
