module

public import Certificates.Kernel.MonsterExist.P5.Lattice
public import Certificates.Kernel.MonsterExist.P5.Fixed

public section

namespace CertificateChecks.MonsterExist.P5

open CFSG.Monster.Existence.StdOdd.P5

set_option Elab.async false

theorem lattice_zero : [0] ∈ lattice := by decide +kernel

theorem lattice_length : lattice.length = 50 := by decide +kernel

theorem latticeNodup : ∀ l ∈ lattice, l.Nodup := by decide +kernel

theorem all_of_slices {α : Type} (f : α → Bool) (c : ℕ) :
    ∀ (K : ℕ) (L : List α), L.length ≤ c * K →
      (∀ k < K, ((L.drop (c * k)).take c).all f = true) → L.all f = true
  | 0, L, hL, _ => by
    rw [List.length_eq_zero_iff.1 (show L.length = 0 by omega)]
    rfl
  | K + 1, L, hL, h => by
    rw [← List.take_append_drop c L, List.all_append, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by omega), all_of_slices f c K _ (by simp; rw [Nat.mul_succ] at hL; omega)
      fun k hk => ?_⟩
    have := h (k + 1) (by omega)
    rwa [List.drop_drop, show c + c * k = c * (k + 1) by ring]

noncomputable abbrev closedAt (k : ℕ) : Bool :=
  ((lattice.drop (5 * k)).take 5).all fun l => (List.finRange 81).all (checkLatM lattice l)

theorem cl0 : closedAt 0 = true := by decide +kernel
theorem cl1 : closedAt 1 = true := by decide +kernel
theorem cl2 : closedAt 2 = true := by decide +kernel
theorem cl3 : closedAt 3 = true := by decide +kernel
theorem cl4 : closedAt 4 = true := by decide +kernel
theorem cl5 : closedAt 5 = true := by decide +kernel
theorem cl6 : closedAt 6 = true := by decide +kernel
theorem cl7 : closedAt 7 = true := by decide +kernel
theorem cl8 : closedAt 8 = true := by decide +kernel
theorem cl9 : closedAt 9 = true := by decide +kernel

theorem latticeClosedB_true : latticeClosedB = true := by
  rw [latticeClosedB_eq]
  refine all_of_slices _ 5 10 lattice (by rw [lattice_length]) fun k hk => ?_
  interval_cases k
  exacts [cl0, cl1, cl2, cl3, cl4, cl5, cl6, cl7, cl8, cl9]

noncomputable abbrev elemM (l : List (Fin 81)) : Bool :=
  !(l.all fun i => decide (tbF (tbF i i) i = 0) && l.all fun j => decide (tbF i j = tbF j i)) ||
    decide (l = [0]) || decide (l.length * fixedCardM l ≤ 81)

noncomputable abbrev elemAt (k : ℕ) : Bool := ((lattice.drop (5 * k)).take 5).all elemM

theorem el0 : elemAt 0 = true := by decide +kernel
theorem el1 : elemAt 1 = true := by decide +kernel
theorem el2 : elemAt 2 = true := by decide +kernel
theorem el3 : elemAt 3 = true := by decide +kernel
theorem el4 : elemAt 4 = true := by decide +kernel
theorem el5 : elemAt 5 = true := by decide +kernel
theorem el6 : elemAt 6 = true := by decide +kernel
theorem el7 : elemAt 7 = true := by decide +kernel
theorem el8 : elemAt 8 = true := by decide +kernel
theorem el9 : elemAt 9 = true := by decide +kernel

theorem elemCheckB_true : elemCheckB = true := by
  unfold elemCheckB elemAbL
  rw [tb_eq_tbF, fixedCardL_eq]
  refine all_of_slices _ 5 10 lattice (by rw [lattice_length]) fun k hk => ?_
  interval_cases k
  exacts [el0, el1, el2, el3, el4, el5, el6, el7, el8, el9]

theorem cert27CheckB_true : cert27CheckB = true := by
  unfold cert27CheckB Cert27Ok closureFin closureStep
  rw [tb_eq_tbF]
  decide +kernel

end CertificateChecks.MonsterExist.P5

end
