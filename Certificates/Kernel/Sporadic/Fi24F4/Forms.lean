module

public import CFSG.Sporadic.Fi24I301.Words
public import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CertificateChecks.KernelSpor.Fi24F4

open CFSG.Sporadic.Fi24I301 Matrix

theorem altMat_add (c d : Fin 10 → ZMod 3) : altMat (c + d) = altMat c + altMat d := by
  ext i j
  simp only [altMat, Pi.add_apply, Matrix.add_apply]
  by_cases h1 : i < j
  · simp only [h1, if_true]
  · by_cases h2 : j < i
    · simp only [h1, h2, if_true, if_false]
      ring
    · simp only [h1, h2, if_false, add_zero]

theorem altMat_smul (a : ZMod 3) (c : Fin 10 → ZMod 3) : altMat (a • c) = a • altMat c := by
  ext i j
  simp only [altMat, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h1 : i < j
  · simp only [h1, if_true]
  · by_cases h2 : j < i
    · simp only [h1, h2, if_true, if_false]
      ring
    · simp only [h1, h2, if_false, mul_zero]

noncomputable def altL : (Fin 10 → ZMod 3) →ₗ[ZMod 3] Matrix (Fin 5) (Fin 5) (ZMod 3) where
  toFun := altMat
  map_add' := altMat_add
  map_smul' := altMat_smul

theorem single_eq_smul {n : ℕ} (i : Fin n) (a : ZMod 3) :
    Pi.single i a = a • (Pi.single i 1 : Fin n → ZMod 3) := by
  rw [← Pi.single_smul, smul_eq_mul, mul_one]

theorem altMat_eq_sum (c : Fin 10 → ZMod 3) :
    altMat c = ∑ i, c i • altMat (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single c]
  change altL (∑ i, Pi.single i (c i)) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [single_eq_smul, map_smul]
  rfl

noncomputable abbrev B (k : Fin 2) (i : Fin 10) : Matrix (Fin 5) (Fin 5) (ZMod 3) :=
  nMat k * altMat (Pi.single i 1) * (nMat k).transpose - altMat (Pi.single i 1)

theorem cond_eq_sum (k : Fin 2) (c : Fin 10 → ZMod 3) :
    nMat k * altMat c * (nMat k).transpose - altMat c = ∑ i, c i • B k i := by
  rw [altMat_eq_sum c, Matrix.mul_sum, Finset.sum_mul]
  simp only [B, smul_sub, Finset.sum_sub_distrib, Matrix.mul_smul, Matrix.smul_mul]

@[expose] def rows : List (Fin 2 × Fin 5 × Fin 5) :=
  [(0, 0, 1), (0, 0, 2), (0, 0, 3), (0, 0, 4), (0, 1, 2), (0, 1, 3), (0, 2, 4), (0, 3, 4),
    (1, 0, 1), (1, 0, 3)]

@[expose] def Linv : List (List (ZMod 3)) :=
  [[2, 0, 0, 0, 1, 1, 0, 0, 2, 0], [2, 0, 1, 2, 0, 2, 2, 1, 1, 0], [1, 2, 0, 0, 2, 0, 2, 2, 0, 2],
    [2, 0, 0, 0, 1, 0, 2, 1, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0, 0, 1, 0],
    [2, 0, 0, 0, 2, 1, 0, 0, 1, 0], [1, 2, 2, 1, 0, 0, 0, 2, 2, 0], [2, 2, 1, 2, 2, 2, 0, 1, 2, 0],
    [2, 2, 2, 2, 0, 1, 2, 1, 1, 2]]

theorem left_inv : ∀ i i' : Fin 10,
    ∑ j : Fin 10, (Linv[i.val]!)[j.val]! *
      B (rows[j.val]!).1 i' (rows[j.val]!).2.1 (rows[j.val]!).2.2 = if i = i' then 1 else 0 := by
  decide

theorem noAltForm : ∀ c : Fin 10 → ZMod 3,
    (∀ k : Fin 2, nMat k * altMat c * (nMat k).transpose = altMat c) → c = 0 := by
  intro c h
  have h0 : ∀ k, ∑ i, c i • B k i = 0 := fun k => by rw [← cond_eq_sum, h k, sub_self]
  funext i
  have e : c i = ∑ j : Fin 10, (Linv[i.val]!)[j.val]! *
      (∑ i', c i' • B (rows[j.val]!).1 i') (rows[j.val]!).2.1 (rows[j.val]!).2.2 := by
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_left_comm _ (c _)]
    simp only [← Finset.mul_sum, left_inv i]
    simp
  rw [e]
  simp only [h0, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, Pi.zero_apply]

noncomputable abbrev V (k : Fin 2) (i : Fin 5) : Fin 5 → ZMod 3 :=
  (nMat k).mulVec (Pi.single i 1) - Pi.single i 1

theorem vcond_eq_sum (k : Fin 2) (q : Fin 5 → ZMod 3) :
    (nMat k).mulVec q - q = ∑ i, q i • V k i := by
  conv_lhs => rw [← Finset.univ_sum_single q]
  change (nMat k).mulVecLin (∑ i, Pi.single i (q i)) - ∑ i, Pi.single i (q i) = _
  rw [map_sum]
  have e : ∀ i, q i • V k i = (nMat k).mulVecLin (Pi.single i (q i)) - Pi.single i (q i) :=
    fun i => by
      rw [single_eq_smul, map_smul, smul_sub]
      rfl
  simp only [e]
  rw [Finset.sum_sub_distrib]

@[expose] def rowsV : List (Fin 2 × Fin 5) := [(0, 0), (0, 1), (0, 3), (0, 4), (1, 2)]

@[expose] def LinvV : List (List (ZMod 3)) :=
  [[0, 0, 0, 0, 1], [0, 1, 0, 0, 0], [1, 1, 2, 0, 0], [1, 2, 0, 2, 1], [0, 0, 1, 1, 2]]

theorem left_invV : ∀ i i' : Fin 5,
    ∑ j : Fin 5, (LinvV[i.val]!)[j.val]! * V (rowsV[j.val]!).1 i' (rowsV[j.val]!).2 =
      if i = i' then 1 else 0 := by
  decide

theorem noLinForm : ∀ q : Fin 5 → ZMod 3, (∀ k : Fin 2, (nMat k).mulVec q = q) → q = 0 := by
  intro q h
  have h0 : ∀ k, ∑ i, q i • V k i = 0 := fun k => by rw [← vcond_eq_sum, h k, sub_self]
  funext i
  have e : q i = ∑ j : Fin 5, (LinvV[i.val]!)[j.val]! *
      (∑ i', q i' • V (rowsV[j.val]!).1 i') (rowsV[j.val]!).2 := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_left_comm _ (q _)]
    simp only [← Finset.mul_sum, left_invV i]
    simp
  rw [e]
  simp only [h0, mul_zero, Finset.sum_const_zero, Pi.zero_apply]

end CertificateChecks.KernelSpor.Fi24F4

end
