module

public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Monster.B.Co2.Native CFSG.KC.Enum

theorem allLt_iff (n : Nat) (p : Nat → Bool) : allLt n p = true ↔ ∀ i < n, p i = true := by
  unfold allLt
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩ (List.mem_finRange _)
  · intro h i _
    exact h i.val i.isLt

theorem eqA_iff (n : Nat) (t u : Array Nat) : eqA n t u = true ↔ ∀ i < n, t[i]! = u[i]! := by
  unfold eqA
  rw [allLt_iff]
  simp

theorem eqA_false {n : Nat} {t u : Array Nat} {i : Nat} (hi : i < n) (h : t[i]! ≠ u[i]!) :
    eqA n t u = false := by
  cases he : eqA n t u
  · rfl
  · exact absurd ((eqA_iff n t u).1 he i hi) h

theorem compA_get {n : Nat} {t u : Array Nat} {i : Nat} (hi : i < n) :
    (compA n t u)[i]! = t[u[i]!]! := by
  rw [getElem!_pos (compA n t u) i (by simp [compA, hi])]
  simp [compA]

theorem idA_get {n i : Nat} (hi : i < n) : (idA n)[i]! = i := by
  rw [getElem!_pos (idA n) i (by simp [idA, hi])]
  simp [idA]

end CertificateChecks.KernelSpor.OddCore

end
