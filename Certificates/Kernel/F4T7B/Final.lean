module

public import Certificates.Kernel.F4T7B.Checks
public import CFSG.Certificates.Kernel.F4T7BSound

public section

namespace CFSG.KD.F4T7B

open CFSG.KC.F4T7B CFSG.RankThree.PartTwo.Sec10.KS1012GL34

theorem lens : C.map List.length = [1080, 1080, 1080, 1080, 1080, 1080] ∧
    K.map List.length = [3, 3, 3, 3, 3, 3] := by
  have h := ch188006_len
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  exact h

theorem getD_length (L : List (List Nat)) (n : Nat) :
    (L.getD n []).length = (L.map List.length).getD n 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[n]? <;> rfl

theorem chk_i (i : Fin 6) : chkAll (omC i.val) (C.getD i.val []) (K.getD i.val []) = true := by
  fin_cases i
  · exact ch188006_0
  · exact ch188006_1
  · exact ch188006_2
  · exact ch188006_3
  · exact ch188006_4
  · exact ch188006_5

theorem lenC (i : Fin 6) : (C.getD i.val []).length = 1080 := by
  rw [getD_length, lens.1]
  fin_cases i <;> rfl

theorem lenK (i : Fin 6) : (K.getD i.val []).length = 3 := by
  rw [getD_length, lens.2]
  fin_cases i <;> rfl

theorem t7Check_eq : t7Check () = true :=
  t7Check_of fun i => ⟨C.getD i.val [], K.getD i.val [], chk_i i, lenC i, lenK i⟩

end CFSG.KD.F4T7B

end
