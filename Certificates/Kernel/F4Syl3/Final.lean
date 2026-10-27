module

public import Certificates.Kernel.F4Syl3.Cls
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.KC.F4Syl3

open CFSG.LieType.Simplicity.TitsBits CFSG.KC.F4Salt CFSG.KC.Loop
  CFSG.RankThree.PartTwo.Sec21.FF81.F4 CFSG.RankThree.PartTwo.Sec21.FF79 CFSG.KD.F4Syl3
  CFSG.LieType.Ree


theorem fS_26 : fS sE 26 = zE := by
  have e : dg 26 0 = 2 ∧ dg 26 1 = 2 ∧ dg 26 2 = 2 ∧ dg 26 3 = 0 := by decide
  rw [fS, e.1, e.2.1, e.2.2.1, e.2.2.2, sE4, pow_zero, mul_one, pow_two, pow_two, pow_two]

theorem trgE_0 : trgE 0 = rAE := if_pos rfl

theorem trgE_1 : trgE 1 = rBE := by simp [trgE]

theorem trgE_2 : trgE 2 = zE := by simp [trgE]

theorem syl3_facts :
    ∃ P : Subgroup F42C, Nat.card P = 3 ^ 6 ∧ Subgroup.closure (Set.range sE) ≤ P ∧
      IsElemAb 3 4 (Subgroup.closure (Set.range sE)) ∧
      (∀ B ≤ P, IsElemAb 3 4 B → B = Subgroup.closure (Set.range sE)) ∧
      (∀ x ∈ P, x * zE = zE * x) ∧
      (∀ x ∈ P, x ≠ 1 → x ^ 3 = 1 → IsConj x rAE ∨ IsConj x rBE ∨ IsConj x zE) ∧
      (∃ LA LB : Finset (Subgroup F42C), LA.card ≤ 12 ∧ LB.card ≤ 12 ∧
        ∀ d ∈ Subgroup.closure (Set.range sE), d ≠ 1 →
          (IsConj d rAE ∧ Subgroup.zpowers d ∈ LA) ∨ (IsConj d rBE ∧ Subgroup.zpowers d ∈ LB) ∨
            IsConj d zE) ∧
      IsConj (ReeTag.F4.finiteExceptionalAut (ZMod 2) rAE) rBE ∧
      ∀ t ∈ [tE, uE, tuE, vE], ∀ ρ ∈ [rAE, rBE], ∃ c : F42C, c * ρ * c⁻¹ * t = t * (c * ρ * c⁻¹) := by
  have hp := pres_F42
  have hm := modelOK_of_chk model_ok
  have hT : IsElemAb 3 4 (Subgroup.closure (Set.range sE)) :=
    ⟨CFSG.IsElementaryAbelian.of_forall (fun _ hx _ hy => T_comm hp hx hy)
      (fun _ hx => T_cube hp hx), by rw [card_T hp hm]; norm_num⟩
  refine ⟨Subgroup.closure (gensP sE g4E g5E), by rw [card_P hp hm]; norm_num, T_le_P _ _ _, hT,
    fun B hB hBe => ?_, fun x hx => ?_, fun x hx h1 h3 => ?_, ?_, phi_link_F42, inv_comm_F42⟩
  · have hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
      intro x hx y hy
      have := hBe.1.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : B) ⟨y, hy⟩
      exact congrArg Subtype.val this
    exact e81_unique hp hm hB hc (by rw [hBe.2]; norm_num)
  · rw [← fS_26]
    exact z_central hp hm hx
  · have h := class_cover hp hm cover_ok trgE rep_conj hx h1 h3
    rwa [trgE_0, trgE_1, trgE_2] at h
  · have h := lines_T hp hm cover_ok line_ok trgE rep_conj
    rwa [trgE_0, trgE_1, trgE_2] at h

end CFSG.KC.F4Syl3

end
