module

public import Certificates.Kernel.HN1408.Tab6PredChk
public import Certificates.Kernel.HN1408.Tab6CntFacts

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Tab6

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KD.HN1408 CFSG.KD.HN1408.CzT
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3Model

theorem repC_powK {X : Nat} {x : Equiv.Perm (Fin 1408)} (hX : RepC X x) :
    ∀ e, RepC (powK X e) (x ^ e)
  | 0 => by
    rw [pow_zero]
    exact repC_idK
  | e + 1 => by
    rw [pow_succ']
    exact repC_pc hX (repC_powK hX e)

theorem eq_of_beq {X Y : Nat} {x y : Equiv.Perm (Fin 1408)} (hX : RepC X x) (hY : RepC Y y)
    (h : Nat.beq X Y = true) : x = y := by
  rw [Nat.eq_of_beq_eq_true h] at hX
  exact eq_of_repC hX hY

theorem ne_one_of_movesK {X : Nat} {x : Equiv.Perm (Fin 1408)} (hX : RepC X x)
    (h : movesK X = true) : x ≠ 1 := by
  intro e
  rw [e] at hX
  unfold movesK at h
  rw [repC_pt hX (by norm_num)] at h
  simp at h

theorem ne_of_pt0 {X Y : Nat} {x y : Equiv.Perm (Fin 1408)} (hX : RepC X x) (hY : RepC Y y)
    (h : (!Nat.beq (pt X 0) (pt Y 0)) = true) : x ≠ y := by
  intro e
  rw [e] at hX
  rw [repC_pt hX (by norm_num), repC_pt hY (by norm_num)] at h
  simp at h

theorem conj_of_conjK {w : List Nat} (hw : lettersOK w = true) (hwr : lettersOK w.reverse = true)
    {S T : Nat} {s t : Equiv.Perm (Fin 1408)} (hS : RepC S s) (hT : RepC T t)
    (h : conjK w S T = true) : elemW w * s * (elemW w)⁻¹ = t := by
  have hr := repC_pc (repC_pc (repC_word hw) hS) (repC_word hwr)
  rw [W441872.elemW_rev hw] at hr
  exact eq_of_beq hr hT h

theorem repC_x (i : Fin 8) :
    RepC (xK (tab6Row i).conj)
      ((wordP wordAZ * (tab6Row i).rowP wordAZ : ↥P1408) : Equiv.Perm (Fin 1408)) :=
  repC_pc (repC_word (by decide)) (repC_row (letters_row i).1 (letters_row i).2)

theorem isConj_of_eq {w : List Nat} {s t : ↥P1408}
    (h : elemW w * (s : Equiv.Perm (Fin 1408)) * (elemW w)⁻¹ = t) : IsConj s t :=
  isConj_iff.2 ⟨wordP w, Subtype.ext h⟩

theorem orderOf_P {x : ↥P1408} {n : ℕ} (h : orderOf (x : Equiv.Perm (Fin 1408)) = n) :
    orderOf x = n := by
  rwa [Subgroup.orderOf_coe] at h

theorem pow_coe (x : ↥P1408) (n : ℕ) :
    ((x ^ n : ↥P1408) : Equiv.Perm (Fin 1408)) = (x : Equiv.Perm (Fin 1408)) ^ n :=
  SubmonoidClass.coe_pow x n

theorem orderOf_six {G : Type} [Group G] {x : G} (h6 : x ^ 6 = 1) (h2 : x ^ 2 ≠ 1)
    (h3 : x ^ 3 ≠ 1) : orderOf x = 6 := by
  have hd : orderOf x ∣ 6 := orderOf_dvd_of_pow_eq_one h6
  have hle : orderOf x ≤ 6 := Nat.le_of_dvd (by norm_num) hd
  have h1 : x ^ orderOf x = 1 := pow_orderOf_eq_one x
  interval_cases h : orderOf x
  · norm_num at hd
  · rw [pow_one] at h1
    exact absurd (by rw [pow_two, h1, one_mul]) h2
  · exact absurd h1 h2
  · exact absurd h1 h3
  · norm_num at hd
  · norm_num at hd
  · rfl

theorem tab6_ne (i : Fin 8) : (tab6Row i).rowP wordAZ ≠ wordP wordAZ := by
  intro e
  have hc := repC_row (letters_row i).1 (letters_row i).2
  have hy : RepC (WK wordAZ) (elemW wordAZ) := repC_word (by decide)
  have hn : (!Nat.beq (pt (WK ((tab6Row i).conj ++ wordAZ ++ (tab6Row i).conj.reverse)) 0)
      (pt (WK wordAZ) 0)) = true := by
    fin_cases i
    · exact ch441694_ne0
    · exact ch441694_ne1
    · exact ch441694_ne2
    · exact ch441694_ne3
    · exact ch441694_ne4
    · exact ch441694_ne5
    · exact ch441694_ne6
    · exact ch441694_ne7
  exact ne_of_pt0 hc hy hn (by rw [← coe_rowP, e]; rfl)

theorem tab6_row0 : IsConj (wordP wordAZ) (wordP wordAZ * (tab6Row 0).rowP wordAZ) :=
  isConj_of_eq (conj_of_conjK (w := tab6W0) (by decide) (by decide) (repC_word (by decide))
    (repC_x 0) ch441694_p0)

theorem tab6_row1 : IsConj (wordP wordZ) (wordP wordAZ * (tab6Row 1).rowP wordAZ) :=
  isConj_of_eq (conj_of_conjK (w := tab6W1) (by decide) (by decide) (repC_word (by decide))
    (repC_x 1) ch441694_p1)

theorem tab6_row2 : orderOf (wordP wordAZ * (tab6Row 2).rowP wordAZ) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_P (orderOf_eq_prime (eq_of_beq (repC_powK (repC_x 2) 3) repC_idK ch441694_p2e)
    (ne_one_of_movesK (repC_x 2) ch441694_p2m))

theorem order4 {x : Equiv.Perm (Fin 1408)} (e4 : x ^ 4 = 1) (n2 : x ^ 2 ≠ 1) : orderOf x = 4 := by
  have h1 : (2 : ℕ) ^ (1 + 1) = 4 := rfl
  have h2 : (2 : ℕ) ^ 1 = 2 := rfl
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := x) (by rw [h2]; exact n2)
    (by rw [h1]; exact e4)
  rwa [h1] at this

theorem tab6_row3 : orderOf (wordP wordAZ * (tab6Row 3).rowP wordAZ) = 4 ∧
    IsConj (wordP wordZ) ((wordP wordAZ * (tab6Row 3).rowP wordAZ) ^ 2) := by
  refine ⟨orderOf_P (order4 (eq_of_beq (repC_powK (repC_x 3) 4) repC_idK ch441694_p3e)
    (ne_one_of_movesK (repC_powK (repC_x 3) 2) ch441694_p3m)), isConj_of_eq (w := tab6W3) ?_⟩
  rw [pow_coe]
  exact conj_of_conjK (w := tab6W3) (by decide) (by decide) (repC_word (by decide))
    (repC_powK (repC_x 3) 2) ch441694_p3c

theorem tab6_row4 : orderOf (wordP wordAZ * (tab6Row 4).rowP wordAZ) = 4 ∧
    IsConj (wordP wordAZ) ((wordP wordAZ * (tab6Row 4).rowP wordAZ) ^ 2) := by
  refine ⟨orderOf_P (order4 (eq_of_beq (repC_powK (repC_x 4) 4) repC_idK ch441694_p4e)
    (ne_one_of_movesK (repC_powK (repC_x 4) 2) ch441694_p4m)), isConj_of_eq (w := tab6W4) ?_⟩
  rw [pow_coe]
  exact conj_of_conjK (w := tab6W4) (by decide) (by decide) (repC_word (by decide))
    (repC_powK (repC_x 4) 2) ch441694_p4c

theorem tab6_row5 : orderOf (wordP wordAZ * (tab6Row 5).rowP wordAZ) = 5 ∧
    IsConj (wordP fix5C.rep) (wordP wordAZ * (tab6Row 5).rowP wordAZ) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine ⟨orderOf_P (orderOf_eq_prime (eq_of_beq (repC_powK (repC_x 5) 5) repC_idK ch441694_p5e)
    (ne_one_of_movesK (repC_x 5) ch441694_p5m)), isConj_of_eq (w := tab6W5) ?_⟩
  exact conj_of_conjK (w := tab6W5) (by decide) (by decide) (repC_word (by decide))
    (repC_x 5) ch441694_p5c

theorem tab6_row6 : orderOf (wordP wordAZ * (tab6Row 6).rowP wordAZ) = 5 ∧
    IsConj (wordP fix5B.rep) (wordP wordAZ * (tab6Row 6).rowP wordAZ) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine ⟨orderOf_P (orderOf_eq_prime (eq_of_beq (repC_powK (repC_x 6) 5) repC_idK ch441694_p6e)
    (ne_one_of_movesK (repC_x 6) ch441694_p6m)), isConj_of_eq (w := tab6W6) ?_⟩
  exact conj_of_conjK (w := tab6W6) (by decide) (by decide) (repC_word (by decide))
    (repC_x 6) ch441694_p6c

theorem tab6_row7 : orderOf (wordP wordAZ * (tab6Row 7).rowP wordAZ) = 6 ∧
    IsConj (wordP wordAZ) ((wordP wordAZ * (tab6Row 7).rowP wordAZ) ^ 3) := by
  refine ⟨orderOf_P (orderOf_six (eq_of_beq (repC_powK (repC_x 7) 6) repC_idK ch441694_p7e)
    (ne_one_of_movesK (repC_powK (repC_x 7) 2) ch441694_p7m2)
    (ne_one_of_movesK (repC_powK (repC_x 7) 3) ch441694_p7m3)), isConj_of_eq (w := tab6W7) ?_⟩
  rw [pow_coe]
  exact conj_of_conjK (w := tab6W7) (by decide) (by decide) (repC_word (by decide))
    (repC_powK (repC_x 7) 3) ch441694_p7c

end CFSG.KD.HN1408.Tab6

end
