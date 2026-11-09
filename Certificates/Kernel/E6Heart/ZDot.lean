module

public import Certificates.Kernel.E6Heart.Twin
import all Certificates.Data.E6Heart
import Mathlib.Tactic.Ring

public section

namespace CertificateChecks.E6HeartK

open Certificates.E6Heart

@[expose] def colS (a : List Int) (j : Nat) : Int :=
  idx6.foldl (fun s i => s + a.getD i 0 * cEntry i j) 0

@[expose] def dotV (v : List Int) (y : List Nat) : Int :=
  idx6.foldl (fun s j => s + v.getD j 0 * ((y.getD j 0 : Nat) : Int)) 0

@[expose] def vT : List (List Int) :=
  [[2, 0, -1, 0, 0, 0],
   [0, 2, 0, -1, 0, 0],
   [-1, 0, 2, -1, 0, 0],
   [0, -1, -1, 2, -1, 0],
   [0, 0, 0, -1, 2, -1],
   [0, 0, 0, 0, -1, 2],
   [-2, 0, 1, 0, 0, 0],
   [1, 0, 1, -1, 0, 0],
   [0, -2, 0, 1, 0, 0],
   [0, 1, -1, 1, -1, 0],
   [1, 0, -2, 1, 0, 0],
   [-1, -1, 1, 1, -1, 0],
   [0, 1, 1, -2, 1, 0],
   [0, -1, -1, 1, 1, -1],
   [0, 0, 0, 1, -2, 1],
   [0, 0, 0, -1, 1, 1],
   [0, 0, 0, 0, 1, -2],
   [-1, 0, -1, 1, 0, 0],
   [1, -1, 0, 1, -1, 0],
   [0, -1, 1, -1, 1, 0],
   [-1, 1, 1, 0, -1, 0],
   [0, 1, -1, 0, 1, -1],
   [1, 1, -1, -1, 1, 0],
   [-1, -1, 1, 0, 1, -1],
   [0, 1, 1, -1, -1, 1],
   [0, -1, -1, 1, 0, 1],
   [0, 0, 0, 1, -1, -1],
   [-1, 1, 0, -1, 1, 0],
   [1, 1, 0, 0, -1, 0],
   [1, -1, 0, 0, 1, -1],
   [1, -1, -1, 0, 1, 0],
   [0, -1, 1, 0, -1, 1],
   [-1, 1, 1, -1, 1, -1],
   [0, 1, -1, 0, 0, 1],
   [1, 1, -1, 0, -1, 1],
   [-1, -1, 1, 0, 0, 1],
   [0, 1, 1, -1, 0, -1],
   [-1, -1, 0, 0, 1, 0],
   [-1, 1, 0, 0, -1, 1],
   [1, 1, 0, -1, 1, -1],
   [1, -1, 0, 0, 0, 1],
   [1, -1, -1, 1, -1, 1],
   [0, -1, 1, 0, 0, -1],
   [-1, 0, 0, 1, 0, -1],
   [-1, 1, 1, -1, 0, 1],
   [1, 1, -1, 0, 0, -1],
   [-1, -1, 0, 1, -1, 1],
   [-1, 1, 0, 0, 0, -1],
   [1, 0, -1, 1, 0, -1],
   [1, 1, 0, -1, 0, 1],
   [1, 0, 0, -1, 0, 1],
   [1, -1, -1, 1, 0, -1],
   [-1, 0, 0, 1, -1, 1],
   [-1, 0, 1, -1, 0, 1],
   [-1, -1, 0, 1, 0, -1],
   [0, 0, 1, 0, 0, -1],
   [1, 0, -1, 1, -1, 1],
   [1, 0, 0, -1, 1, -1],
   [-1, 0, 0, 0, 1, 0],
   [0, 0, -1, 0, 0, 1],
   [-1, 0, 1, -1, 1, -1],
   [0, 0, 1, 0, -1, 1],
   [1, 0, -1, 0, 1, 0],
   [1, 0, 0, 0, -1, 0],
   [0, 0, -1, 0, 1, -1],
   [-1, 0, 1, 0, -1, 0],
   [0, 0, 1, -1, 1, 0],
   [0, 0, -1, 1, -1, 0],
   [0, -1, 0, 1, 0, 0],
   [0, 1, 0, -1, 0, 0],
   [0, 1, 0, 0, 0, 0],
   [0, -1, 0, 0, 0, 0]]

@[expose] noncomputable def nthV (P : List (List Int)) : Nat → List Int :=
  List.rec (motive := fun _ => Nat → List Int) (fun _ => [])
    (fun p _ ih i => Nat.rec (motive := fun _ => List Int) p (fun j _ => ih j) i) P

@[expose] noncomputable def vOk : Bool :=
  (List.range 72).all fun i => idx6.map (colS (rootAt i)) == nthV vT i

@[expose] noncomputable def zOkV : Bool :=
  (List.range 72).all fun i => (List.range 243).all fun t =>
    (m3 (dotV (nthV vT i) (repL t)) == 0) == bitN (nthN zT i) t

theorem getD_map_cast (y : List Nat) (j : Nat) :
    (y.map (fun u : Nat => (u : Int))).getD j 0 = ((y.getD j 0 : Nat) : Int) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases y[j]? <;> rfl

theorem pair3_eq (a : List Int) (y : List Nat) : pair3 a y = m3 (dotV (idx6.map (colS a)) y) := by
  unfold pair3
  congr 1
  simp only [pairZ, dotV, colS, idx6, List.foldl, List.map, getD_map_cast, List.getD_cons_zero,
    List.getD_cons_succ]
  ring

@[expose] def dotI (v b : List Int) : Int := idx6.foldl (fun s j => s + v.getD j 0 * b.getD j 0) 0

@[expose] noncomputable def adjOkV : Bool :=
  (List.range 72).all fun i => (List.range 72).all fun j =>
    (i != j && dotI (nthV vT i) (rootAt j) != 0) == bitN (nthN adjT i) j

theorem pairZ_eq (a b : List Int) : pairZ a b = dotI (idx6.map (colS a)) b := by
  simp only [pairZ, dotI, colS, idx6, List.foldl, List.map, List.getD_cons_zero,
    List.getD_cons_succ]
  ring

theorem adjOk_of (hv : vOk = true) (ha : adjOkV = true) : adjOk = true := by
  unfold adjOk
  rw [List.all_eq_true]
  intro i hi
  rw [List.all_eq_true]
  intro j hj
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 ha i hi) j hj
  have hv1 := beq_iff_eq.1 (List.all_eq_true.1 hv i hi)
  rw [adjB, pairZ_eq, hv1]
  exact h1

theorem zOk_of (hv : vOk = true) (hz : zOkV = true) : zOk = true := by
  unfold zOk
  rw [List.all_eq_true]
  intro i hi
  rw [List.all_eq_true]
  intro t ht
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 hz i hi) t ht
  have hv1 := beq_iff_eq.1 (List.all_eq_true.1 hv i hi)
  rw [pair3_eq, hv1]
  exact h1

end CertificateChecks.E6HeartK
