module

public import Certificates.Data.Kernel.G2Three.Recog
public import Certificates.Kernel.G2Three.SylFinal
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G2Three

open CFSG.KC.G2Three CFSG.KC.Ord CFSG.RankThree.PartTwo.Census.Carrier.G2Three
  CFSG.GH74.QTGen4.Recog.G23 CFSG.GH74.QTGen4.Recog.G23.P7 CFSG.Sporadic.Th.Recog

@[expose] def recLetter (l : Fin 6 × Bool) : ℕ := pk (CFSG.GH74.QTGen4.Recog.G23.letterCode l)

theorem recTri_ok : recTriK recLetter = true := by quickRfl

theorem recTh_ok : recThK recLetter = true := by quickRfl

theorem evalCode_pk (w : List (Fin 6 × Bool)) :
    canon14 (evalCode w) = true ∧ pk (evalCode w) = wordF recLetter w := by
  unfold evalCode wordF
  exact foldl_pk consts_ok CFSG.GH74.QTGen4.Recog.G23.letterCode recLetter letter_pk w one14 ONE
    ⟨canon14_one14, bone⟩

theorem evalCode_eq {a b : List (Fin 6 × Bool)}
    (h : Nat.beq (wordF recLetter a) (wordF recLetter b) = true) : evalCode a = evalCode b :=
  pk_inj (evalCode_pk a).1 (evalCode_pk b).1 (by
    rw [(evalCode_pk a).2, (evalCode_pk b).2]
    exact Nat.eq_of_beq_eq_true h)

theorem evalCode_eq_one {a : List (Fin 6 × Bool)} (h : Nat.beq (wordF recLetter a) ONE = true) :
    evalCode a = one14 :=
  pk_inj (evalCode_pk a).1 canon14_one14 (by
    rw [(evalCode_pk a).2, bone]
    exact Nat.eq_of_beq_eq_true h)

theorem evalCode_ne_one {a : List (Fin 6 × Bool)} (h : Nat.beq (wordF recLetter a) ONE = false) :
    evalCode a ≠ one14 := by
  intro he
  have hp := (evalCode_pk a).2
  rw [he, bone] at hp
  rw [← hp, Nat.beq_refl] at h
  exact Bool.noConfusion h

theorem ok320014 : (∀ r ∈ triWords, evalCode (substTri r) = one14) ∧
    (∀ i, evalCode (substTri (triEWord i)) = eCode i) := by
  have h := recTri_ok
  unfold recTriK at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  refine ⟨fun r hr => evalCode_eq_one (h.1 r hr), fun i => ?_⟩
  have hi := h.2 i (List.mem_finRange i)
  exact pk_inj (evalCode_pk _).1 (letter_pk (i, true)).1 (by
    rw [(evalCode_pk _).2]
    exact Nat.eq_of_beq_eq_true hi)

theorem ok687007 :
    evalCode (z0Word ++ z0Word) = one14 ∧
    evalCode z0Word ≠ one14 ∧
    (∀ i : Fin 5, evalCode (z0Word ++ [(Fin.castSucc i, true)]) =
      evalCode ((Fin.castSucc i, true) :: z0Word)) ∧
    (∀ r ∈ g23PD, evalCode (substWord (dEmbed r)) = one14) ∧
    evalCode (substWord d2mWord) ≠ one14 ∧
    evalCode (substWord (List.flatten (List.replicate 7 d2mWord))) = one14 := by
  have h := recTh_ok
  unfold recThK at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨evalCode_eq_one h1, evalCode_ne_one h2,
    fun i => evalCode_eq (h3 i (List.mem_finRange i)), fun r hr => evalCode_eq_one (h4 r hr),
    evalCode_ne_one h5, evalCode_eq_one h6⟩

end CFSG.KD.G2Three

end
