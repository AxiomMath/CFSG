module

public import Certificates.Kernel.EvenSporG24Hex.Data
public import Certificates.Kernel.EvenSporG24.TblText
import all Init.Data.List.SplitOn.Basic
import Certificates.Kernel.EvenSporG24Hex.Fast
import CFSG.Certificates.Kernel.F3152.SortSound
import Mathlib.Data.List.Sort
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelG24Hex

open CFSG.KC.EvenSporG24Hex CertificateChecks.EvenSporG24

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
theorem dataOK_true : dataOK tblL D.U D.W D.GE D.PG = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem linesOK_true : linesOK D.U D.W = true := by
  rw [linesOK_eq]
  decide +kernel

private theorem insN_eq' (a : ℕ) : ∀ l : List ℕ, insN a l = l.orderedInsert (· ≤ ·) a
  | [] => by rw [insN, List.orderedInsert_nil]
  | b :: l => by rw [insN, List.orderedInsert_cons, insN_eq' a l]

private theorem isortN_eq' : ∀ l : List ℕ, isortN l = l.insertionSort (· ≤ ·)
  | [] => by rw [isortN, List.insertionSort_nil]
  | b :: l => by rw [isortN, List.insertionSort_cons, isortN_eq' l, insN_eq']

private theorem strictInc_of_pairwise : ∀ l : List ℕ, l.Pairwise (· < ·) → strictInc l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    have hab : a < b := List.rel_of_pairwise_cons h List.mem_cons_self
    simp only [strictInc, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hab, strictInc_of_pairwise (b :: l) h.of_cons⟩

private theorem strictInc_isortN {l : List ℕ}
    (h : CFSG.KS.F3152.sortedK (CFSG.KS.F3152.msortK l) = true) : strictInc (isortN l) = true := by
  have hp := CFSG.KS.F3152.sortedK_pairwise _ h
  have hs : (isortN l).Pairwise (· ≤ ·) := by
    rw [isortN_eq']
    exact List.pairwise_insertionSort _ l
  have hq : (isortN l).Perm l := by
    rw [isortN_eq']
    exact List.perm_insertionSort _ l
  have he : isortN l = CFSG.KS.F3152.msortK l :=
    List.Perm.eq_of_pairwise (fun a b _ _ hab hba => Nat.le_antisymm hab hba) hs
      (hp.imp Nat.le_of_lt) (hq.trans (CFSG.KS.F3152.msortK_perm l).symm)
  rw [he]
  exact strictInc_of_pairwise _ hp

set_option maxHeartbeats 0 in
theorem keysOK_true : keysOK D.U D.W = true := by
  rw [keysOK_eq]
  exact strictInc_isortN (by quickRfl)

set_option maxHeartbeats 0 in
theorem lcOK_true : lcOK D.U D.W D.LC = true := by
  rw [lcOK_eq]
  decide +kernel

end CertificateChecks.KernelG24Hex
