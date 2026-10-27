module

public import Certificates.Kernel.SporSch.Tits.Graph2265N
public import Certificates.Kernel.SporSch.Tits.Graph2265R0
public import Certificates.Kernel.SporSch.Tits.Graph2265R2
public import Certificates.Kernel.SporSch.Tits.Graph2265R3
public import Certificates.Kernel.SporSch.Tits.Graph2265R4
public import Certificates.Kernel.SporSch.Tits.Graph2265R5
public import Certificates.Kernel.SporSch.Tits.Graph2265R6
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.TitsGraph

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native

theorem stepEq {t t' k : Nat} (h : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST t) (TitsGS.ST t')
    (TitsGS.SC t) (TitsGS.PI t) (TitsGS.REP t') k = true) :
    refineStep (unpack 1755 11 (TitsGS.ST t)) = unpack 1755 11 (TitsGS.ST t') := by
  rw [refineStep_eq]
  exact refK_sound nbr_eq h

theorem initEq {i t : Nat} (h : allN 1755 (fun x => Nat.beq (pgW 11 (TitsGS.ST t) x)
    (if (titsIndiv.take i).contains x then (titsIndiv.take i).idxOf x + 1 else 0)) = true) :
    initColor i = unpack 1755 11 (TitsGS.ST t) := by
  apply Array.ext
  · simp [initColor, unpack]
  · intro x h1 _
    have hx : x < 1755 := by simpa [initColor] using h1
    have e := Nat.eq_of_beq_eq_true (allN_spec h x hx)
    simp only [initColor, unpack, Array.getElem_ofFn]
    rw [← pgW_eq, e]

theorem iter_chain {f : Array ℕ → Array ℕ} {g : ℕ → Array ℕ} :
    ∀ {r : ℕ}, (∀ j < r, f (g j) = g (j + 1)) → f^[r] (g 0) = g r
  | 0, _ => rfl
  | r + 1, h => by
    rw [Function.iterate_succ_apply', iter_chain fun j hj => h j (by omega), h r (by omega)]

theorem stable0 : stableColor 0 = unpack 1755 11 (TitsGS.ST 0) := by
  unfold stableColor
  rw [initEq kI0]
  rfl

theorem stable1 : stableColor 1 = unpack 1755 11 (TitsGS.ST 5) := by
  have h := iter_chain (f := refineStep) (g := fun j => unpack 1755 11 (TitsGS.ST (2 + j)))
    (r := 3) fun j hj => by
      interval_cases j
      · exact stepEq kR2
      · exact stepEq kR3
      · exact stepEq kR4
  unfold stableColor
  rw [initEq kI1]
  exact h

theorem stable2 : stableColor 2 = unpack 1755 11 (TitsGS.ST 13) := by
  have h := iter_chain (f := refineStep) (g := fun j => unpack 1755 11 (TitsGS.ST (7 + j)))
    (r := 6) fun j hj => by
      interval_cases j
      · exact stepEq kR7
      · exact stepEq kR8
      · exact stepEq kR9
      · exact stepEq kR10
      · exact stepEq kR11
      · exact stepEq kR12
  unfold stableColor
  rw [initEq kI2]
  exact h

theorem stable3 : stableColor 3 = unpack 1755 11 (TitsGS.ST 22) := by
  have h := iter_chain (f := refineStep) (g := fun j => unpack 1755 11 (TitsGS.ST (15 + j)))
    (r := 7) fun j hj => by
      interval_cases j
      · exact stepEq kR15
      · exact stepEq kR16
      · exact stepEq kR17
      · exact stepEq kR18
      · exact stepEq kR19
      · exact stepEq kR20
      · exact stepEq kR21
  unfold stableColor
  rw [initEq kI3]
  exact h

theorem stable4 : stableColor 4 = unpack 1755 11 (TitsGS.ST 30) := by
  have h := iter_chain (f := refineStep) (g := fun j => unpack 1755 11 (TitsGS.ST (24 + j)))
    (r := 6) fun j hj => by
      interval_cases j
      · exact stepEq kR24
      · exact stepEq kR25
      · exact stepEq kR26
      · exact stepEq kR27
      · exact stepEq kR28
      · exact stepEq kR29
  unfold stableColor
  rw [initEq kI4]
  exact h

theorem stable5 : stableColor 5 = unpack 1755 11 (TitsGS.ST 38) := by
  have h := iter_chain (f := refineStep) (g := fun j => unpack 1755 11 (TitsGS.ST (32 + j)))
    (r := 6) fun j hj => by
      interval_cases j
      · exact stepEq kR32
      · exact stepEq kR33
      · exact stepEq kR34
      · exact stepEq kR35
      · exact stepEq kR36
      · exact stepEq kR37
  unfold stableColor
  rw [initEq kI5]
  exact h

theorem stable6 : stableColor 6 = unpack 1755 11 (TitsGS.ST 46) := by
  have h := iter_chain (f := refineStep) (g := fun j => unpack 1755 11 (TitsGS.ST (40 + j)))
    (r := 6) fun j hj => by
      interval_cases j
      · exact stepEq kR40
      · exact stepEq kR41
      · exact stepEq kR42
      · exact stepEq kR43
      · exact stepEq kR44
      · exact stepEq kR45
  unfold stableColor
  rw [initEq kI6]
  exact h

theorem unpack_size (P : Nat) : (unpack 1755 11 P).size = 1755 := by
  simp [unpack]

theorem cell {t i x c : Nat} (hi : titsIndiv[i]! = x) (hx : x < 1755)
    (h : Nat.beq (cntK 1755 11 (TitsGS.ST t) (pgW 11 (TitsGS.ST t) x)) c = true) :
    cellSize (unpack 1755 11 (TitsGS.ST t)) titsIndiv[i]! = c := by
  rw [hi, cellSize_eq hx]
  exact Nat.eq_of_beq_eq_true h

theorem ok0 : refineOK 0 (stableColor 0) = true := by
  rw [stable0]
  unfold refineOK
  rw [stepEq kR0, numK_sound kC0, numK_sound kC0', unpack_size,
    cell (i := 0) (x := 1) rfl (by norm_num) kS0]
  rfl

theorem ok1 : refineOK 1 (stableColor 1) = true := by
  rw [stable1]
  unfold refineOK
  rw [stepEq kR5, numK_sound kC1, numK_sound kC1', unpack_size,
    cell (i := 1) (x := 3) rfl (by norm_num) kS1]
  rfl

theorem ok2 : refineOK 2 (stableColor 2) = true := by
  rw [stable2]
  unfold refineOK
  rw [stepEq kR13, numK_sound kC2, numK_sound kC2', unpack_size,
    cell (i := 2) (x := 6) rfl (by norm_num) kS2]
  rfl

theorem ok3 : refineOK 3 (stableColor 3) = true := by
  rw [stable3]
  unfold refineOK
  rw [stepEq kR22, numK_sound kC3, numK_sound kC3', unpack_size,
    cell (i := 3) (x := 5) rfl (by norm_num) kS3]
  rfl

theorem ok4 : refineOK 4 (stableColor 4) = true := by
  rw [stable4]
  unfold refineOK
  rw [stepEq kR30, numK_sound kC4, numK_sound kC4', unpack_size,
    cell (i := 4) (x := 12) rfl (by norm_num) kS4]
  rfl

theorem ok5 : refineOK 5 (stableColor 5) = true := by
  rw [stable5]
  unfold refineOK
  rw [stepEq kR38, numK_sound kC5, numK_sound kC5', unpack_size,
    cell (i := 5) (x := 24) rfl (by norm_num) kS5]
  rfl

theorem ok6 : refineOK 6 (stableColor 6) = true := by
  rw [stable6]
  unfold refineOK
  rw [stepEq kR46, numK_sound kC6, numK_sound kC6', unpack_size]
  rfl

theorem facts : ((∀ u < 1755, (titsNbr[u]!).size = 10 ∧ (titsNbrLine[u]!).size = 10 ∧
        (titsNbr[u]!).toList.Pairwise (· < ·) ∧
        ∀ i < 10, (titsNbr[u]!)[i]! < 1755 ∧ (titsNbr[u]!)[i]! ≠ u ∧ (titsNbrLine[u]!)[i]! < 2925 ∧
          ptsHas (titsNbrLine[u]!)[i]! u = true ∧
          ptsHas (titsNbrLine[u]!)[i]! (titsNbr[u]!)[i]! = true) ∧
      (∀ v < 2925, ∀ k < 3, ∀ k' < 3, k ≠ k' →
        (titsNbr[titsLinePtArr[3 * v + k]!]!).contains titsLinePtArr[3 * v + k']! = true) ∧
      (titsNbr[0]!).contains 1 = true) ∧
    ((∀ i < 7, refineOK i (stableColor i) = true) ∧
      ((stableColor 6).toList.mergeSort fun a b => decide (a ≤ b)).Pairwise (· < ·)) := by
  refine ⟨graphFacts, fun i hi => ?_, ?_⟩
  · interval_cases i
    · exact ok0
    · exact ok1
    · exact ok2
    · exact ok3
    · exact ok4
    · exact ok5
    · exact ok6
  · rw [stable6]
    exact distK_sound kC6

end CertificateChecks.KernelSporSch.TitsGraph

end
