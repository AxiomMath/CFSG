module

public import Certificates.Kernel.Misc.E6StdBridge
public import Certificates.Kernel.StdOdd.Reps
public import Certificates.Kernel.StdOdd.SlpCmd
public import CFSG.Monster.Existence.StdOdd.Cert.Sylow57Inputs
import all CFSG.Monster.Existence.StdOdd.Cert.Sylow57Data
meta import CFSG.Monster.Existence.StdOdd.Cert.Sylow57Data
meta import Certificates.Kernel.Misc.E6StdData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LieType.Chevalley.C2E6ExactRootRestrictions
public import CFSG.LieType.Chevalley.C2E6NativeF4Building
public import CFSG.LieType.Chevalley.GraphFixedParabolicLevi
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Monster.Existence.StdOdd.Cert.Base

public section

namespace CFSG.KD.StdOdd.Sylow57

open CFSG.KC.Misc CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.E6Std CFSG.KD.Misc.E6Std CFSG.KD.StdOdd.Reps
  CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std.MatrixModel
  CFSG.Monster.Existence.StdOdd.Cert

set_option maxRecDepth 100000

theorem rep_mul' {a b : ℕ} {P Q : Native.Mat} (ha : Rep a (toMat P)) (hb : Rep b (toMat Q)) :
    Rep (mulB a b) (toMat (Native.mul P Q)) := by
  rw [toMat_mul]
  exact rep_mulB ha hb

theorem rep_pow' {a : ℕ} {P : Native.Mat} (n : ℕ) (ha : Rep a (toMat P)) :
    Rep (powB a n) (toMat (Native.pow P n)) := by
  rw [toMat_pow]
  exact rep_powB ha n

theorem fusion_of_blow {p : ℕ} {X Y : Native.Mat} {C r : ℕ → Native.Mat} {x y : ℕ}
    {c rr : ℕ → ℕ} (hX : Rep x (toMat X)) (hY : Rep y (toMat Y))
    (hC : ∀ i < p, Rep (c i) (toMat (C i))) (hr : ∀ i < p, Rep (rr i) (toMat (r i)))
    (h1 : ordB y p = true) (h2 : Nat.beq (mulB x y) (mulB y x) = true)
    (h3 : allN p (fun k => notB (Nat.beq (powB x k) y)) = true)
    (h4 : ∀ i < p, Nat.beq (mulB (c i) (rr i)) (mulB (mulB (powB x i) y) (c i)) = true) :
    sylowFusionCheck p X Y C r = true := by
  unfold sylowFusionCheck
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨ordP_of_ordB hY h1, ?_⟩, fun k hk => ?_⟩, fun i hi => ?_⟩
  · rw [eqM_iff_of_rep (rep_mul' hX hY) (rep_mul' hY hX)]
    exact h2
  · have h := allN_true h3 k hk
    rw [notB_eq'] at h
    rw [eqM_iff_of_rep (rep_pow' k hX) hY]
    exact h
  · rw [eqM_iff_of_rep (rep_mul' (hC i hi) (hr i hi)) (rep_mul' (rep_mul' (rep_pow' i hX) hY)
      (hC i hi))]
    exact h4 i hi

theorem rep_word (v : List (ℕ × Bool)) (k : ℕ) :
    Rep (powB (wordB (nthV Fvals idxA) (nthV Fvals idxB) v) k)
      (toMat (Native.wordMat nativeAB.1 nativeAB.2 (wordPow v k))) := by
  rw [toMat_wordPow]
  exact rep_powB (rep_wordB rep_A rep_B v) k

theorem rep_vals_gen {X Y : Native.Mat} {a b : ℕ} (hX : Rep a (toMat X)) (hY : Rep b (toMat Y))
    {V : List ℕ} {prog : List (List ℕ)}
    (h0 : Nat.beq (nthV V 0) a = true) (h1 : Nat.beq (nthV V 1) b = true)
    (hp : ∀ t < lenLL prog, slpLine V prog 2 t = true)
    (hn : Nat.beq (lenN V) (Nat.add 2 (lenLL prog)) = true) {i : ℕ}
    (hi : Nat.blt i (lenN V) = true) :
    Rep (nthV V i) (toMat ((Native.slpRun #[X, Y] prog).getD i Native.one)) := by
  have hG : ∀ i < (#[X, Y] : Array Native.Mat).size,
      Rep (nthV V i) (toMat ((#[X, Y] : Array Native.Mat).getD i Native.one)) := by
    intro i hi
    change i < 2 at hi
    rcases i with _ | _ | i
    · exact rep_of_eq hX h0
    · exact rep_of_eq hY h1
    · omega
  rw [Nat.beq_eq] at hn
  rw [Nat.blt_eq] at hi
  exact rep_run hG hp i (by change i < 2 + lenLL prog; change lenN V = 2 + lenLL prog at hn; omega)

theorem rep_vals {V : List ℕ} {prog : List (List ℕ)}
    (h0 : Nat.beq (nthV V 0) (nthV Fvals idxA) = true)
    (h1 : Nat.beq (nthV V 1) (nthV Fvals idxB) = true)
    (hp : ∀ t < lenLL prog, slpLine V prog 2 t = true)
    (hn : Nat.beq (lenN V) (Nat.add 2 (lenLL prog)) = true) {i : ℕ}
    (hi : Nat.blt i (lenN V) = true) :
    Rep (nthV V i) (toMat ((Native.slpRun #[nativeAB.1, nativeAB.2] prog).getD i Native.one)) :=
  rep_vals_gen rep_A rep_B h0 h1 hp hn hi

#e6_slp S5 sylow5Prog Fvals 3 14

theorem S5.v0 : Nat.beq (nthV S5.V 0) (nthV Fvals idxA) = true := by quickRfl
theorem S5.v1 : Nat.beq (nthV S5.V 1) (nthV Fvals idxB) = true := by quickRfl
theorem S5.len : Nat.beq (lenN S5.V) (Nat.add 2 (lenLL sylow5Prog)) = true := by quickRfl
theorem S5.yLt : Nat.blt sylow5Y (lenN S5.V) = true := by quickRfl
theorem S5.cLt : allN 5 (fun i => Nat.blt (nthV sylow5Conj i) (lenN S5.V)) = true := by quickRfl

@[expose] noncomputable def x5 : ℕ := powB (wordB (nthV Fvals idxA) (nthV Fvals idxB) b5) 6

@[expose] noncomputable def y5 : ℕ := nthV S5.V sylow5Y

@[expose] noncomputable def c5 (i : ℕ) : ℕ := nthV S5.V (nthV sylow5Conj i)

theorem S5.ord : ordB y5 5 = true := by quickRfl
theorem S5.comm : Nat.beq (mulB x5 y5) (mulB y5 x5) = true := by quickRfl
theorem S5.notPow : allN 5 (fun k => notB (Nat.beq (powB x5 k) y5)) = true := by quickRfl
theorem S5.conj :
    allN 5 (fun i => Nat.beq (mulB (c5 i) x5) (mulB (mulB (powB x5 i) y5) (c5 i))) = true := by
  quickRfl

theorem sylow5 : sylow5Check = true := by
  have hX : Rep x5 (toMat (Native.wordMat nativeAB.1 nativeAB.2 repWord5)) := by
    rw [repWord5, e5]
    exact rep_word b5 6
  unfold sylow5Check
  refine fusion_of_blow (c := c5) (rr := fun _ => x5) hX
    (rep_vals S5.v0 S5.v1 S5.lines S5.len S5.yLt) (fun i hi => ?_) (fun _ _ => hX) S5.ord S5.comm
    S5.notPow (allN_true S5.conj)
  rw [← nthV_eq_getD]
  exact rep_vals S5.v0 S5.v1 S5.lines S5.len (allN_true S5.cLt i hi)

#e6_slp S7 sylow7Prog Fvals 3 14

theorem S7.v0 : Nat.beq (nthV S7.V 0) (nthV Fvals idxA) = true := by quickRfl
theorem S7.v1 : Nat.beq (nthV S7.V 1) (nthV Fvals idxB) = true := by quickRfl
theorem S7.len : Nat.beq (lenN S7.V) (Nat.add 2 (lenLL sylow7Prog)) = true := by quickRfl
theorem S7.zLt : Nat.blt sylow7Z (lenN S7.V) = true := by quickRfl
theorem S7.cLt : allN 7 (fun i => Nat.blt (nthV sylow7Conj i) (lenN S7.V)) = true := by quickRfl

@[expose] noncomputable def x7 : ℕ := powB (wordB (nthV Fvals idxA) (nthV Fvals idxB) b7B) 4

@[expose] noncomputable def xa7 : ℕ := powB (wordB (nthV Fvals idxA) (nthV Fvals idxB) b7A) 5

@[expose] noncomputable def z7 : ℕ := nthV S7.V sylow7Z

@[expose] noncomputable def c7 (i : ℕ) : ℕ := nthV S7.V (nthV sylow7Conj i)

theorem S7.ord : ordB z7 7 = true := by quickRfl
theorem S7.comm : Nat.beq (mulB x7 z7) (mulB z7 x7) = true := by quickRfl
theorem S7.notPow : allN 7 (fun k => notB (Nat.beq (powB x7 k) z7)) = true := by quickRfl
theorem S7.conj0 : Nat.beq (mulB (c7 0) x7) (mulB (mulB (powB x7 0) z7) (c7 0)) = true := by
  quickRfl
theorem S7.conj1 : Nat.beq (mulB (c7 1) xa7) (mulB (mulB (powB x7 1) z7) (c7 1)) = true := by
  quickRfl
theorem S7.conj2 : Nat.beq (mulB (c7 2) xa7) (mulB (mulB (powB x7 2) z7) (c7 2)) = true := by
  quickRfl
theorem S7.conj3 : Nat.beq (mulB (c7 3) xa7) (mulB (mulB (powB x7 3) z7) (c7 3)) = true := by
  quickRfl
theorem S7.conj4 : Nat.beq (mulB (c7 4) x7) (mulB (mulB (powB x7 4) z7) (c7 4)) = true := by
  quickRfl
theorem S7.conj5 : Nat.beq (mulB (c7 5) xa7) (mulB (mulB (powB x7 5) z7) (c7 5)) = true := by
  quickRfl
theorem S7.conj6 : Nat.beq (mulB (c7 6) x7) (mulB (mulB (powB x7 6) z7) (c7 6)) = true := by
  quickRfl

theorem sylow7 : sylow7Check = true := by
  have hX : Rep x7 (toMat (Native.wordMat nativeAB.1 nativeAB.2 repWord7B)) := by
    rw [repWord7B, e7B]
    exact rep_word b7B 4
  have hXA : Rep xa7 (toMat (Native.wordMat nativeAB.1 nativeAB.2 repWord7A)) := by
    rw [repWord7A, e7A]
    exact rep_word b7A 5
  unfold sylow7Check
  refine fusion_of_blow (c := c7) (rr := fun i => if sylow7IsA.getD i false = true then xa7 else x7)
    hX (rep_vals S7.v0 S7.v1 S7.lines S7.len S7.zLt) (fun i hi => ?_) (fun i _ => ?_) S7.ord
    S7.comm S7.notPow (fun i hi => ?_)
  · rw [← nthV_eq_getD]
    exact rep_vals S7.v0 S7.v1 S7.lines S7.len (allN_true S7.cLt i hi)
  · by_cases h : sylow7IsA.getD i false = true
    · simp only [h, ↓reduceIte]
      exact hXA
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      exact hX
  · interval_cases i
    exacts [S7.conj0, S7.conj1, S7.conj2, S7.conj3, S7.conj4, S7.conj5, S7.conj6]

theorem facts : sylow5Check = true ∧ sylow7Check = true := ⟨sylow5, sylow7⟩

end CFSG.KD.StdOdd.Sylow57

end
