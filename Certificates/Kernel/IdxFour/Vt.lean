module

public import Certificates.Kernel.IdxFour.Lbar
public import CFSG.Certificates.Kernel.IdxFourTcosetSound

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.KD.IF4L

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.IF4L CFSG.KC.IF4T CFSG.GF2Type.Smith1979.GammaU
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.IdxFour
open CFSG.RankThree.OrthogonalInvolutions

theorem selOK_spec {B : List ℕ} : ∀ {l cs : List ℕ}, selOK B l cs = true →
    ∀ x ∈ l, ∃ c, x = xsel B c
  | [], _, _, x, hx => absurd hx List.not_mem_nil
  | _ :: _, [], h, _, _ => absurd h Bool.false_ne_true
  | y :: l, c :: cs, h, x, hx => by
    change (Nat.beq y (xsel B c) && selOK B l cs) = true at h
    rw [Bool.and_eq_true, Nat.beq_eq] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨c, h.1⟩
    · exact selOK_spec h.2 x hx

theorem vecOf_xsel_mem {S : Set V12} : ∀ {B : List ℕ}, (∀ b ∈ B, vecOf b ∈ S) →
    ∀ c, vecOf (xsel B c) ∈ Submodule.span (ZMod 2) S
  | [], _, _ => by
    change vecOf 0 ∈ _
    rw [vecOf_zero]
    exact zero_mem _
  | b :: B, h, c => by
    change vecOf (Nat.xor (bif Nat.beq (Nat.mod c 2) 1 then b else 0) (xsel B (Nat.div c 2))) ∈ _
    change vecOf ((bif Nat.beq (c % 2) 1 then b else 0) ^^^ xsel B (c / 2)) ∈ _
    rw [vecOf_xor]
    refine add_mem ?_ (vecOf_xsel_mem (fun b' hb' => h b' (List.mem_cons_of_mem _ hb')) _)
    cases Nat.beq (c % 2) 1
    · rw [cond_false, vecOf_zero]
      exact zero_mem _
    · exact Submodule.subset_span (h b List.mem_cons_self)

theorem mem_imgs {LP WB : List ℕ} {x : ℕ} (hx : x ∈ imgs LP WB) :
    ∃ l ∈ LP, ∃ w ∈ WB, x = ap12 l w ^^^ w := by
  induction LP with
  | nil => exact absurd hx List.not_mem_nil
  | cons l LP ih =>
    have key : ∀ (W : List ℕ), x ∈ List.rec (motive := fun _ => List ℕ) (imgs LP WB)
        (fun w _ r => Nat.xor (ap12 l w) w :: r) W →
        x ∈ imgs LP WB ∨ ∃ w ∈ W, x = ap12 l w ^^^ w := by
      intro W
      induction W with
      | nil => exact Or.inl
      | cons w W ihW =>
        intro hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact Or.inr ⟨w, List.mem_cons_self, rfl⟩
        · rcases ihW hx with h | ⟨w', hw', e⟩
          · exact Or.inl h
          · exact Or.inr ⟨w', List.mem_cons_of_mem _ hw', e⟩
    rcases key WB hx with h | ⟨w, hw, e⟩
    · obtain ⟨l', hl', w, hw, e⟩ := ih h
      exact ⟨l', List.mem_cons_of_mem _ hl', w, hw, e⟩
    · exact ⟨l, List.mem_cons_self, w, hw, e⟩

theorem f0_eq_zero_of_f0K {x y : ℕ} (h : f0K x y = false) : f0 (vecOf x) (vecOf y) = 0 := by
  rw [f0_vecOf, ← f0K_eq, h]
  rfl

theorem vt_le : spanOf vtBasis ≤ Submodule.span (ZMod 2) {y | ∃ l ∈ genGrp lbarGens, ∃ x : V12,
    f0 x (vecOf 15) = 0 ∧ f0 x (vecOf 960) = 0 ∧ y = l x - x} := by
  have h := cf17608w
  unfold wOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hA, hB⟩, -⟩, hD⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  rw [List.all_eq_true] at hA hB
  have hW : ∀ x, inW 15 960 x = true →
      f0 (vecOf x) (vecOf 15) = 0 ∧ f0 (vecOf x) (vecOf 960) = 0 := fun x hx => by
    change (!f0K x 15 && !f0K x 960) = true at hx
    rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true'] at hx
    exact ⟨f0_eq_zero_of_f0K hx.1, f0_eq_zero_of_f0K hx.2⟩
  have himg : ∀ b ∈ imgs (lbarGens.map packR) WB, vecOf b ∈ {y | ∃ l ∈ genGrp lbarGens,
      ∃ x : V12, f0 x (vecOf 15) = 0 ∧ f0 x (vecOf 960) = 0 ∧ y = l x - x} := by
    intro b hb
    obtain ⟨g, hg, w, hw, rfl⟩ := mem_imgs hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    have hi' : i < lbarL.length := by rw [lbar_F.length_eq]; exact hi
    have hP := isP_getD lbar_F i hi'
    rw [List.getD_eq_getElem _ _ hi] at hP
    obtain ⟨h1, h2⟩ := hW w (hA w hw)
    refine ⟨lbarL[i], ?_, vecOf w, h1, h2, ?_⟩
    · rw [genGrp_lbar]
      exact Subgroup.subset_closure (List.getElem_mem hi')
    · rw [vecOf_xor, IsP.apply_code hP, vec_sub_eq_add]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨c, rfl⟩ := selOK_spec hD v hv
  exact vecOf_xsel_mem himg c

end CFSG.KD.IF4L

end
