
module

public import Certificates.Kernel.SporSch.HN.Pt2108Defs
public import Certificates.Kernel.SporSch.HN.Pt2108Tab
public import CFSG.Sporadic.HNSchreier.SylowCheckInputs
public import CFSG.Sporadic.HNSchreier.ThreeCheckInputs
public import Certificates.Kernel.LocalQT.Tc.Gen
public import CFSG.Sporadic.Schreier.ONPermArr
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib.Data.Vector.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import Std.Tactic.BVDecide.Normalize.Prop

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNPt2108

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KC.LL.HNXT4 CFSG.KC.LL.HNXSyl
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier.Native
open CFSG.KD.HNPt2108

theorem lift_data : FAData.pLift.size = 5 ∧
    (∀ j < 5, ∀ l ∈ FAData.pLift[j]!, 1 ≤ l ∧ l ≤ 7) ∧
    (∀ l ∈ FAData.pKernel, l ≠ 0 ∧ l.natAbs ≤ 17) := by decide +kernel

theorem par_data : FAData.pParents.size = 729 ∧ FAData.pParents[0]! = (0, 0) ∧
    ∀ i < 729, i ≠ 0 → (FAData.pParents[i]!).1 < i ∧ (FAData.pParents[i]!).2 < 6 := by
  decide +kernel

private theorem all_get {α : Type} [Inhabited α] {a : Array α} {p : α → Bool}
    (h : a.toList.all p = true) {i : Nat} (hi : i < a.size) : p a[i]! = true := by
  rw [getElem!_pos a i hi]
  exact List.all_eq_true.1 h _ (Array.getElem_mem_toList hi)

private theorem rows_of {T : Array (Array Nat)} {n m : Nat} (hs : T.size = n)
    (h : T.toList.all (fun a => a.size == m && a.toList.all fun x => decide (x < m)) = true) :
    ∀ j < n, (T[j]!).size = m ∧ ∀ i < m, (T[j]!)[i]! < m := by
  intro j hj
  have hj' := all_get h (i := j) (by rw [hs]; exact hj)
  simp only [Bool.and_eq_true, beq_iff_eq] at hj'
  exact ⟨hj'.1, fun i hi => of_decide_eq_true (all_get hj'.2 (by rw [hj'.1]; exact hi))⟩

theorem left_data : ∀ j < 6, (FAData.pLeft[j]!).size = 729 ∧
    ∀ i < 729, (FAData.pLeft[j]!)[i]! < 729 :=
  rows_of (by decide +kernel) (by decide +kernel)

theorem conj_data : ∀ j < 6, (SylowData.conj[j]!).size = 729 ∧
    ∀ i < 729, (SylowData.conj[j]!)[i]! < 729 :=
  rows_of (by decide +kernel) (by decide +kernel)

theorem rep_data : ∀ c < 48, FAData.wRep[c]! < 729 ∧
    (∀ l ∈ FAData.wRoot[c]!, l = 1 ∨ l = 2) ∧ (∀ l ∈ FAData.wHWord[c]!, l ≠ 0 ∧ l.natAbs ≤ 17) := by
  decide +kernel

theorem base_len : Data.baseList.length = 22 := by decide

theorem order3_zero : SylowData.order3.contains 0 = false := by decide +kernel

theorem w0_lt : allN 132 (fun k => Nat.blt (f14 (WRf 0) k) 15312) = true := by quickRfl

theorem cy_lt : allN 729 (fun i => Nat.blt (f21 CY i) 1140000) = true := by quickRfl

theorem tab_data :
    FAData.c3Words.size = 6 ∧ (∀ j < 6, plettersOK 17 FAData.c3Words[j]! = true) ∧
    plettersOK 17 FAData.g3H = true ∧ (FAData.g3Root.all fun l => l == 1 || l == 2) = true ∧
    plettersOK 17 FAData.pKernel = true ∧ FAData.pLift.size = 5 ∧
    FAData.pLeft.size = 6 ∧ SylowData.order3.length = 512 ∧ SylowData.conj.size = 6 ∧
    FAData.wClass.size = 48 ∧ SylowData.tree.size = 729 ∧ FAData.wRep.size = 48 ∧
    FAData.wRoot.size = 48 ∧ FAData.wHWord.size = 48 ∧ FAData.wNat.size = 48 ∧
    FAData.wCycles.size = 48 ∧ SylowData.rho.size = 48 := by
  decide +kernel

@[expose] def labL : Array Nat :=
  (List.range' 0 48).foldl (fun lab c => (FAData.wClass[c]!).foldl (fun lab i => lab.set! i c) lab)
    (Array.replicate 729 48)

@[expose] def markL : Array Bool := Array.ofFn (n := 729) fun i => SylowData.order3.contains i.val

theorem labels_eq : classLabels FAData.wClass = labL := by
  unfold classLabels
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl, pure_bind, bind_pure]
  rfl

theorem cls_size : labL.size = 729 := by decide +kernel

theorem labP : (labL.toList == (List.range 729).map (lane LB 6 63)) = true := by quickRfl

theorem labL_get (i : Nat) : labL[i]! = lane LB 6 63 i :=
  arr_get labP (fun _ hi => lane_of_shift (n := 729) (Nat.eq_of_beq_eq_true (by quickRfl)) hi) i

theorem markP : (SylowData.order3 ==
    (List.range 729).filter fun i => Nat.beq (lane MK 1 1 i) 1) = true := by quickRfl

theorem markL_get (i : Nat) : markL[i]! = Nat.beq (lane MK 1 1 i) 1 := by
  have hL := beq_iff_eq.1 markP
  by_cases hi : i < 729
  · rw [markL, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, hL]
    simp [hi]
    rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.beq_eq]
  · rw [getElem!_neg _ i (by rw [markL, Array.size_ofFn]; omega),
      lane_of_shift (n := 729) (Nat.eq_of_beq_eq_true (by quickRfl)) (by omega)]
    rfl

theorem treeP : (SylowData.tree.toList ==
    (List.range 729).map fun i => (lane TP 10 1023 i, lane TL 3 7 i)) = true := by quickRfl

theorem tree_get (i : Nat) : SylowData.tree[i]! = (lane TP 10 1023 i, lane TL 3 7 i) :=
  arr_get treeP (fun _ hi => by
    rw [lane_of_shift (n := 729) (Nat.eq_of_beq_eq_true (by quickRfl)) hi,
      lane_of_shift (n := 729) (Nat.eq_of_beq_eq_true (by quickRfl)) hi]
    rfl) i

@[expose] def treeReachF (t : Nat → Nat × Nat) : Nat → Nat → Bool
  | 0, _ => false
  | f + 1, i => (t i).2 == 0 || treeReachF t f (t i).1

theorem treeReach_eq {tr : Array (Nat × Nat)} {t : Nat → Nat × Nat} (h : ∀ i, tr[i]! = t i)
    (f i : Nat) : treeReach tr f i = treeReachF t f i := by
  induction f generalizing i with
  | zero => rfl
  | succ f ih => rw [treeReach, treeReachF, h, ih]

theorem cls_a : ((List.range 48).all fun c => FAData.wClass[c]!.all fun i =>
    decide (i < 729) && markL[i]! && labL[i]! == c &&
      (List.range 6).all fun j => labL[(SylowData.conj[j]!)[i]!]! == c) = true := by
  simp only [markL_get, labL_get, conj_get]
  decide +kernel

theorem cls_b : ((List.range 729).all fun i => !markL[i]! ||
    decide (labL[i]! < 48) && FAData.wClass[labL[i]!]!.contains i) = true := by
  simp only [markL_get, labL_get]
  decide +kernel

theorem cls_c : ((List.range 729).all fun i => !markL[i]! ||
    treeReach SylowData.tree 729 i &&
      if (SylowData.tree[i]!).2 = 0 then i == FAData.wRep[labL[i]!]!
      else decide ((SylowData.tree[i]!).1 < 729) && decide ((SylowData.tree[i]!).2 ≤ 6) &&
        markL[(SylowData.tree[i]!).1]! && labL[(SylowData.tree[i]!).1]! == labL[i]! &&
        (SylowData.conj[(SylowData.tree[i]!).2 - 1]!)[(SylowData.tree[i]!).1]! == i) = true := by
  simp only [treeReach_eq tree_get, tree_get, markL_get, labL_get, conj_get]
  decide +kernel

theorem allBelowN_eq (n : Nat) (p : Nat → Bool) : allBelowN n p = (List.range n).all p := by
  apply Bool.eq_iff_iff.2
  rw [CFSG.ONSchreier.allBelowN_iff, List.all_eq_true]
  simp [List.mem_range]

theorem wit_data : ∀ c < 48, FAData.wRep[c]! < 729 ∧ labL[FAData.wRep[c]!]! = c ∧
    (FAData.wRoot[c]!.all fun l => l == 1 || l == 2) = true ∧ plettersOK 17 FAData.wHWord[c]! = true ∧
    1 ≤ FAData.wCycles[c]! ∧ FAData.wCycles[c]! ≤ 4 := by
  simp only [labL_get]
  decide +kernel

end CertificateChecks.KernelSporSch.HNPt2108

end
