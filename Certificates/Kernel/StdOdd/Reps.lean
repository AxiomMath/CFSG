module

public import Certificates.Kernel.Misc.E6StdSlp
public import CFSG.Monster.Existence.StdOdd.Cert.RepsInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Monster.Existence.StdOdd.Defs
public import CFSG.Monster.GMS.Facts.TableV

public section

namespace CFSG.KD.StdOdd.Reps

open CFSG.KC.Misc CFSG.KC.Misc.E6Std CFSG.KD.Misc.E6Std CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel CFSG.Monster.Existence.StdOdd.Cert

set_option maxRecDepth 100000

theorem toMat_wordMat_foldl (X Y : Native.Mat) (w : List (ℕ × Bool)) (P : Native.Mat) :
    toMat (w.foldl (fun acc l => Native.mul acc (Native.signedMat X Y l)) P) =
      toMat P * toMat (Native.wordMat X Y w) := by
  induction w generalizing P with
  | nil => simp [Native.wordMat, toMat_one]
  | cons l w ih =>
    have e : Native.wordMat X Y (l :: w) =
        w.foldl (fun acc l => Native.mul acc (Native.signedMat X Y l))
          (Native.mul Native.one (Native.signedMat X Y l)) := rfl
    rw [List.foldl_cons, ih, e, ih, toMat_mul, toMat_mul, toMat_one, one_mul, mul_assoc]

theorem toMat_wordMat_append (X Y : Native.Mat) (v w : List (ℕ × Bool)) :
    toMat (Native.wordMat X Y (v ++ w)) = toMat (Native.wordMat X Y v) * toMat (Native.wordMat X Y w) := by
  rw [Native.wordMat, List.foldl_append, toMat_wordMat_foldl]
  rfl

theorem toMat_wordPow (X Y : Native.Mat) (v : List (ℕ × Bool)) (k : ℕ) :
    toMat (Native.wordMat X Y (wordPow v k)) = toMat (Native.wordMat X Y v) ^ k := by
  induction k with
  | zero => simp [wordPow, Native.wordMat, toMat_one]
  | succ k ih =>
    have e : wordPow v (k + 1) = wordPow v k ++ v := by
      simp [wordPow, List.replicate_succ', List.flatten_append]
    rw [e, toMat_wordMat_append, ih, pow_succ]

theorem ordP_wordPow {v : List (ℕ × Bool)} {k p : ℕ}
    (h : ordB (powB (wordB (nthV Fvals idxA) (nthV Fvals idxB) v) k) p = true) :
    Native.ordP (Native.wordMat nativeAB.1 nativeAB.2 (wordPow v k)) p = true := by
  refine ordP_of_ordB ?_ h
  rw [toMat_wordPow]
  exact rep_powB (rep_wordB rep_A rep_B v) k

theorem wordPow_one (v : List (ℕ × Bool)) : wordPow v 1 = v := by
  simp [wordPow]

@[expose] def b5 : List (ℕ × Bool) := [(0, true), (1, false), (0, true), (1, true), (0, true),
  (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true),
  (1, true), (0, true), (1, false)]
@[expose] def b7A : List (ℕ × Bool) := [(0, true), (1, true), (0, true), (1, true), (0, true),
  (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true),
  (1, true), (0, true), (1, false), (0, true), (1, true)]
@[expose] def b7B : List (ℕ × Bool) := [(0, true), (1, false), (0, true), (1, true), (0, true),
  (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
  (1, true), (0, true), (1, true), (0, true), (1, true)]
@[expose] def b11 : List (ℕ × Bool) := [(0, true), (1, false), (0, true), (1, false), (0, true),
  (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true),
  (1, false), (0, true), (1, true)]
@[expose] def b13 : List (ℕ × Bool) := [(0, true), (1, false), (0, true), (1, false), (0, true),
  (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true),
  (1, false), (0, true), (1, false)]
@[expose] def b17 : List (ℕ × Bool) := [(0, true), (1, false), (0, true), (1, false), (0, true),
  (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true),
  (1, true), (0, true), (1, false), (0, true), (1, false)]
@[expose] def b19 : List (ℕ × Bool) := [(0, true), (1, true), (0, true), (1, false), (0, true),
  (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true),
  (1, false), (0, true), (1, false)]

theorem e5 : wordOfString "AbABAbAbABAbABAb" = b5 := by decide
theorem e7A : wordOfString "ABABAbAbABAbABAbAB" = b7A := by decide
theorem e7B : wordOfString "AbABAbABABAbABABAB" = b7B := by decide
theorem e11 : wordOfString "AbAbAbAbAbABAbAB" = b11 := by decide
theorem e13 : wordOfString "AbAbAbAbABABAbAb" = b13 := by decide
theorem e17 : wordOfString "AbAbAbAbABAbABAbAb" = b17 := by decide
theorem e19 : wordOfString "ABAbAbAbAbAbAbAb" = b19 := by decide

theorem ord5 : ordB (powB (wordB (nthV Fvals idxA) (nthV Fvals idxB) b5) 6) 5 = true := by
  quickRfl
theorem ord7A : ordB (powB (wordB (nthV Fvals idxA) (nthV Fvals idxB) b7A) 5) 7 = true := by
  quickRfl
theorem ord7B : ordB (powB (wordB (nthV Fvals idxA) (nthV Fvals idxB) b7B) 4) 7 = true := by
  quickRfl
theorem ord11 : ordB (powB (wordB (nthV Fvals idxA) (nthV Fvals idxB) b11) 3) 11 = true := by
  quickRfl
theorem ord13 : ordB (powB (wordB (nthV Fvals idxA) (nthV Fvals idxB) b13) 1) 13 = true := by
  quickRfl
theorem ord17 : ordB (powB (wordB (nthV Fvals idxA) (nthV Fvals idxB) b17) 1) 17 = true := by
  quickRfl
theorem ord19 : ordB (powB (wordB (nthV Fvals idxA) (nthV Fvals idxB) b19) 1) 19 = true := by
  quickRfl

theorem facts :
    (Native.ordP (Native.wordMat nativeAB.1 nativeAB.2 repWord5) 5 = true)
    ∧ (Native.ordP (Native.wordMat nativeAB.1 nativeAB.2 repWord7A) 7 = true)
    ∧ (Native.ordP (Native.wordMat nativeAB.1 nativeAB.2 repWord7B) 7 = true)
    ∧ (Native.ordP (Native.wordMat nativeAB.1 nativeAB.2 repWord11) 11 = true)
    ∧ (Native.ordP (Native.wordMat nativeAB.1 nativeAB.2 repWord13) 13 = true)
    ∧ (Native.ordP (Native.wordMat nativeAB.1 nativeAB.2 repWord17) 17 = true)
    ∧ (Native.ordP (Native.wordMat nativeAB.1 nativeAB.2 repWord19) 19 = true) := by
  have h13 := ordP_wordPow ord13
  have h17 := ordP_wordPow ord17
  have h19 := ordP_wordPow ord19
  rw [wordPow_one] at h13 h17 h19
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [repWord5, e5]; exact ordP_wordPow ord5
  · rw [repWord7A, e7A]; exact ordP_wordPow ord7A
  · rw [repWord7B, e7B]; exact ordP_wordPow ord7B
  · rw [repWord11, e11]; exact ordP_wordPow ord11
  · rw [repWord13, e13]; exact h13
  · rw [repWord17, e17]; exact h17
  · rw [repWord19, e19]; exact h19

end CFSG.KD.StdOdd.Reps

end
