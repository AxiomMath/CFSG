
module

public import Certificates.Kernel.HN1408.CoverFacts
public import Certificates.Kernel.HN1408.ClsBFacts
public import Certificates.Kernel.HN1408.ClsZ1Facts
public import Certificates.Kernel.HN1408.InvFixFacts

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.CzInv

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem conjClass_eq_of_mem {x y : Equiv.Perm (Fin 1408)} (h : x ∈ conjClass P1408 y) :
    conjClass P1408 x = conjClass P1408 y := by
  obtain ⟨c, hc, rfl⟩ := mem_conjClass.1 h
  ext w
  constructor
  · intro hw
    obtain ⟨d, hd, rfl⟩ := mem_conjClass.1 hw
    exact mem_conjClass.2 ⟨d * c, mul_mem hd hc, by group⟩
  · intro hw
    obtain ⟨d, hd, rfl⟩ := mem_conjClass.1 hw
    exact mem_conjClass.2 ⟨d * c⁻¹, mul_mem hd (inv_mem hc), by group⟩

theorem not_mem_of_ncard {x y : Equiv.Perm (Fin 1408)}
    (h : (conjClass P1408 x).ncard ≠ (conjClass P1408 y).ncard) : x ∉ conjClass P1408 y :=
  fun hm => h (by rw [conjClass_eq_of_mem hm])

theorem class_a_card : (conjClass P1408 elemA).ncard = 1 := by
  have ha := basic_ab.2.2.1
  have e : conjClass P1408 elemA = {elemA} := by
    ext w
    rw [Set.mem_singleton_iff]
    constructor
    · intro hw
      obtain ⟨c, hc, rfl⟩ := mem_conjClass.1 hw
      rw [← ha c hc, mul_assoc, mul_inv_cancel, mul_one]
    · rintro rfl
      exact mem_conjClass.2 ⟨1, one_mem _, by group⟩
  rw [e, Set.ncard_singleton]

theorem classes_distinctK (hP : Nat.card ↥P1408 = 177408000) :
    elemA ≠ elemZ ∧ elemA ≠ elemA * elemZ ∧ elemA ≠ elemB ∧ elemA ≠ elemZ₁ ∧
      elemA * elemZ ∉ conjClass P1408 elemZ ∧ elemB ∉ conjClass P1408 elemZ ∧
      elemZ₁ ∉ conjClass P1408 elemZ ∧ elemB ∉ conjClass P1408 (elemA * elemZ) ∧
      elemZ₁ ∉ conjClass P1408 (elemA * elemZ) ∧ elemZ₁ ∉ conjClass P1408 elemB := by
  have ha := basic_ab.2.2.1
  have cA := class_a_card
  have cZ := CzT.class_z_card hP
  have cAZ := CzT.class_az_card hP ha
  have cB := (ClsR.b_facts hP).1
  have cZ1 := (Cz1T.z1_facts hP).1
  have ne : ∀ x : Equiv.Perm (Fin 1408), (conjClass P1408 x).ncard ≠ 1 → elemA ≠ x :=
    fun x h e => h (by rw [← e, cA])
  refine ⟨ne _ (by omega), ne _ (by omega), ne _ (by omega), ne _ (by omega), ?_,
    not_mem_of_ncard (by omega), not_mem_of_ncard (by omega), not_mem_of_ncard (by omega),
    not_mem_of_ncard (by omega), not_mem_of_ncard (by omega)⟩
  intro hm
  obtain ⟨c, -, hc⟩ := mem_conjClass.1 hm
  exact not_conj_z_az c hc.symm

theorem not_isConj_K (hP : Nat.card ↥P1408 = 177408000) :
    ∀ i j : Fin 5, i ≠ j →
      ¬ IsConj (![pA, pZ, pA * pZ, pB, pZ₁] i) (![pA, pZ, pA * pZ, pB, pZ₁] j) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := classes_distinctK hP
  have hcentral := basic_ab.2.2.1
  have nc : ∀ X Y : ↥P1408, (Y : Equiv.Perm (Fin 1408)) ∉ conjClass P1408 (X : Equiv.Perm (Fin 1408)) →
      ¬ IsConj X Y := fun X Y h hc => h ((isConj_iff_mem_conjClass P1408 X Y).1 hc)
  have hA : ∀ y : ↥P1408, IsConj pA y → y = pA := by
    intro y hy
    obtain ⟨g, hg, hyg⟩ := (isConj_iff_mem_conjClass P1408 pA y).1 hy
    apply Subtype.ext
    rw [hyg]
    change g * elemA * g⁻¹ = elemA
    rw [← hcentral g hg, mul_assoc, mul_inv_cancel, mul_one]
  have na : ∀ y : ↥P1408, y ≠ pA → ¬ IsConj pA y := fun y hy hc => hy (hA y hc)
  have na' : ∀ y : ↥P1408, y ≠ pA → ¬ IsConj y pA := fun y hy hc => na y hy hc.symm
  have nc' : ∀ X Y : ↥P1408, (Y : Equiv.Perm (Fin 1408)) ∉ conjClass P1408 (X : Equiv.Perm (Fin 1408)) →
      ¬ IsConj Y X := fun X Y h hc => h ((isConj_iff_mem_conjClass P1408 X Y).1 hc.symm)
  have e1 : pZ ≠ pA := fun h => d1 (congrArg Subtype.val h).symm
  have e2 : pA * pZ ≠ pA := fun h => d2 (congrArg Subtype.val h).symm
  have e3 : pB ≠ pA := fun h => d3 (congrArg Subtype.val h).symm
  have e4 : pZ₁ ≠ pA := fun h => d4 (congrArg Subtype.val h).symm
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact na pZ e1
  · exact na (pA * pZ) e2
  · exact na pB e3
  · exact na pZ₁ e4
  · exact na' pZ e1
  · exact absurd rfl hij
  · exact nc pZ (pA * pZ) d5
  · exact nc pZ pB d6
  · exact nc pZ pZ₁ d7
  · exact na' (pA * pZ) e2
  · exact nc' pZ (pA * pZ) d5
  · exact absurd rfl hij
  · exact nc (pA * pZ) pB d8
  · exact nc (pA * pZ) pZ₁ d9
  · exact na' pB e3
  · exact nc' pZ pB d6
  · exact nc' (pA * pZ) pB d8
  · exact absurd rfl hij
  · exact nc pB pZ₁ d10
  · exact na' pZ₁ e4
  · exact nc' pZ pZ₁ d7
  · exact nc' (pA * pZ) pZ₁ d9
  · exact nc' pB pZ₁ d10
  · exact absurd rfl hij

theorem involution_cover_K (hP : Nat.card ↥P1408 = 177408000) :
    ∀ x : ↥P1408, orderOf x = 2 → ∃ i : Fin 5, IsConj (![pA, pZ, pA * pZ, pB, pZ₁] i) x := by
  intro x hx
  have hxv : orderOf (x : Equiv.Perm (Fin 1408)) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have h2 : (x : Equiv.Perm (Fin 1408)) * x = 1 := by
    rw [← sq, ← hxv, pow_orderOf_eq_one]
  have h1 : (x : Equiv.Perm (Fin 1408)) ≠ 1 := fun e => by
    rw [e, orderOf_one] at hxv
    cases hxv
  obtain ⟨t, ht, c, hc, e⟩ := involution_cover hP x.2 h2 h1
  refine ⟨⟨t, ht⟩, (isConj_iff_mem_conjClass P1408 _ x).2 (mem_conjClass.2 ⟨c, hc, ?_⟩)⟩
  rw [e]
  congr 2
  interval_cases t <;> simp [namedA, namedE, pA, pZ, pB, pZ₁]

end CFSG.KD.HN1408.CzInv

end
