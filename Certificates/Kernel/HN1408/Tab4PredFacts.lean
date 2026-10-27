module

public import Certificates.Kernel.HN1408.Tab4PredChk
public import Certificates.Kernel.HN1408.Tab4CntFacts
public import Certificates.Kernel.HN1408.Tab6PredFacts

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Tab4

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KD.HN1408 CFSG.KD.HN1408.Tab6
open CFSG.KD.HN1408.CbT CFSG.KD.HN1408.CzT
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3Model

theorem ne_of_ne01K {X Y : Nat} {x y : Equiv.Perm (Fin 1408)} (hX : RepC X x) (hY : RepC Y y)
    (h : ne01K X Y = true) : x ≠ y := by
  intro e
  rw [e] at hX
  unfold ne01K at h
  rw [repC_pt hX (by norm_num : (0 : Nat) < 1408), repC_pt hX (by norm_num : (1 : Nat) < 1408),
    repC_pt hY (by norm_num : (0 : Nat) < 1408), repC_pt hY (by norm_num : (1 : Nat) < 1408),
    Nat.beq_refl, Nat.beq_refl] at h
  exact Bool.false_ne_true h

theorem repC_xB (i : Fin 6) :
    RepC (xB (tab4Row i).conj)
      ((wordP wordB * (tab4Row i).rowP wordB : ↥P1408) : Equiv.Perm (Fin 1408)) :=
  repC_pc (repC_word (by decide)) (repC_rowB (letters_row i).1 (letters_row i).2)

theorem repC_ab : RepC (pc (WK wordA) (WK wordB))
    ((wordP wordA * wordP wordB : ↥P1408) : Equiv.Perm (Fin 1408)) :=
  repC_pc (repC_word (by decide)) (repC_word (by decide))

theorem tab4_ne (i : Fin 6) :
    (tab4Row i).rowP wordB ≠ wordP wordB ∧ (tab4Row i).rowP wordB ≠ wordP wordA * wordP wordB := by
  have hc := repC_rowB (letters_row i).1 (letters_row i).2
  have hy : RepC (WK wordB) (elemW wordB) := repC_word (by decide)
  have hb : ne01K (WK ((tab4Row i).conj ++ wordB ++ (tab4Row i).conj.reverse)) (WK wordB) =
      true := by
    fin_cases i
    · exact ch441693_nb0
    · exact ch441693_nb1
    · exact ch441693_nb2
    · exact ch441693_nb3
    · exact ch441693_nb4
    · exact ch441693_nb5
  have hab : ne01K (WK ((tab4Row i).conj ++ wordB ++ (tab4Row i).conj.reverse))
      (pc (WK wordA) (WK wordB)) = true := by
    fin_cases i
    · exact ch441693_nab0
    · exact ch441693_nab1
    · exact ch441693_nab2
    · exact ch441693_nab3
    · exact ch441693_nab4
    · exact ch441693_nab5
  refine ⟨fun e => ne_of_ne01K hc hy hb (by rw [← coe_rowP, e]; rfl), fun e => ?_⟩
  exact ne_of_ne01K hc repC_ab hab (by rw [← coe_rowP, e])

theorem tab4_ab : IsConj (wordP wordB) (wordP wordA * wordP wordB) :=
  isConj_of_eq (conj_of_conjK (w := tab4Wab) (by decide) (by decide) (repC_word (by decide))
    repC_ab ch441693_ab)

theorem tab4_row0 : IsConj (wordP wordAZ) (wordP wordB * (tab4Row 0).rowP wordB) :=
  isConj_of_eq (conj_of_conjK (w := tab4W0) (by decide) (by decide) (repC_word (by decide))
    (repC_xB 0) ch441693_p0)

theorem tab4_row1 : IsConj (wordP wordZ) (wordP wordB * (tab4Row 1).rowP wordB) :=
  isConj_of_eq (conj_of_conjK (w := tab4W1) (by decide) (by decide) (repC_word (by decide))
    (repC_xB 1) ch441693_p1)

theorem tab4_row2 : (wordP wordB * (tab4Row 2).rowP wordB) ^ 2 = wordP wordA := by
  refine Subtype.ext ?_
  rw [pow_coe]
  exact eq_of_beq (repC_powK (repC_xB 2) 2) (repC_word (by decide)) ch441693_p2

theorem tab4_row3 : IsConj (wordP wordZ) ((wordP wordB * (tab4Row 3).rowP wordB) ^ 2) := by
  refine isConj_of_eq (w := tab4W3) ?_
  rw [pow_coe]
  exact conj_of_conjK (w := tab4W3) (by decide) (by decide) (repC_word (by decide))
    (repC_powK (repC_xB 3) 2) ch441693_p3

theorem tab4_row4 : orderOf (wordP wordB * (tab4Row 4).rowP wordB) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_P (orderOf_eq_prime (eq_of_beq (repC_powK (repC_xB 4) 3) repC_idK ch441693_p4e)
    (ne_one_of_movesK (repC_xB 4) ch441693_p4m))

theorem tab4_row5 : (wordP wordB * (tab4Row 5).rowP wordB) ^ 3 = wordP wordA := by
  refine Subtype.ext ?_
  rw [pow_coe]
  exact eq_of_beq (repC_powK (repC_xB 5) 3) (repC_word (by decide)) ch441693_p5

end CFSG.KD.HN1408.Tab4

end
