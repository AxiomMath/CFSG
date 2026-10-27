module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSixAutTests

public section

namespace CertificateChecks.KernelLC.SixAut

open Equiv Equiv.Perm CFSG.ComponentClassification.RankTwoAlt

@[expose] def invo0 : List (Perm (Fin 6)) :=
  [swap 0 1 * swap 2 3, swap 0 1 * swap 2 4, swap 0 1 * swap 2 5, swap 0 1 * swap 3 4,
    swap 0 1 * swap 3 5, swap 0 1 * swap 4 5, swap 0 2 * swap 1 3, swap 0 2 * swap 1 4,
    swap 0 2 * swap 1 5]

@[expose] def invo1 : List (Perm (Fin 6)) :=
  [swap 0 2 * swap 3 4, swap 0 2 * swap 3 5, swap 0 2 * swap 4 5, swap 0 3 * swap 1 2,
    swap 0 3 * swap 1 4, swap 0 3 * swap 1 5, swap 0 3 * swap 2 4, swap 0 3 * swap 2 5,
    swap 0 3 * swap 4 5]

@[expose] def invo2 : List (Perm (Fin 6)) :=
  [swap 0 4 * swap 1 2, swap 0 4 * swap 1 3, swap 0 4 * swap 1 5, swap 0 4 * swap 2 3,
    swap 0 4 * swap 2 5, swap 0 4 * swap 3 5, swap 0 5 * swap 1 2, swap 0 5 * swap 1 3,
    swap 0 5 * swap 1 4]

@[expose] def invo3 : List (Perm (Fin 6)) :=
  [swap 0 5 * swap 2 3, swap 0 5 * swap 2 4, swap 0 5 * swap 3 4, swap 1 2 * swap 3 4,
    swap 1 2 * swap 3 5, swap 1 2 * swap 4 5, swap 1 3 * swap 2 4, swap 1 3 * swap 2 5,
    swap 1 3 * swap 4 5]

@[expose] def invo4 : List (Perm (Fin 6)) :=
  [swap 1 4 * swap 2 3, swap 1 4 * swap 2 5, swap 1 4 * swap 3 5, swap 1 5 * swap 2 3,
    swap 1 5 * swap 2 4, swap 1 5 * swap 3 4, swap 2 3 * swap 4 5, swap 2 4 * swap 3 5,
    swap 2 5 * swap 3 4]

theorem invo_cover : ∀ a : Perm (Fin 6), a * a = 1 → a ≠ 1 → sign a = 1 →
    a ∈ invo0 ++ invo1 ++ invo2 ++ invo3 ++ invo4 := by
  decide +kernel

theorem pair0 : ∀ a ∈ invo0, ∀ b : Perm (Fin 6), PairGood a b := by decide +kernel

theorem pair1 : ∀ a ∈ invo1, ∀ b : Perm (Fin 6), PairGood a b := by decide +kernel

theorem pair2 : ∀ a ∈ invo2, ∀ b : Perm (Fin 6), PairGood a b := by decide +kernel

theorem pair3 : ∀ a ∈ invo3, ∀ b : Perm (Fin 6), PairGood a b := by decide +kernel

theorem pair4 : ∀ a ∈ invo4, ∀ b : Perm (Fin 6), PairGood a b := by decide +kernel

theorem invGood : ∀ a : Perm (Fin 6), InvGood a := by
  intro a h1 h2 h3 b
  have hm := invo_cover a h1 h2 h3
  simp only [List.mem_append] at hm
  rcases hm with (((h | h) | h) | h) | h
  · exact pair0 a h b
  · exact pair1 a h b
  · exact pair2 a h b
  · exact pair3 a h b
  · exact pair4 a h b

theorem actsAsC : ∀ y : Perm (Fin 6), ActsAsC y := by decide +kernel

theorem normThree : ∀ y : Perm (Fin 6), NormThree y := by decide +kernel

theorem sqFour : ∀ y : Perm (Fin 6), SqFour y := by decide +kernel

theorem centSix : ∀ b : Perm (Fin 6), CentSix b := by decide +kernel

theorem sixAutCheck_eq : sixAutCheck = true := by
  unfold sixAutCheck
  rw [decide_eq_true invGood, decide_eq_true actsAsC, decide_eq_true normThree,
    decide_eq_true sqFour, decide_eq_true centSix]
  decide +kernel

end CertificateChecks.KernelLC.SixAut

end
