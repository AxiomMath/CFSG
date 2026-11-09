module

public import Certificates.Kernel.E6Heart.Twin
import all Certificates.Data.E6Heart

public section

namespace CertificateChecks.E6HeartK

open Certificates.E6Heart

@[expose] noncomputable def mOf (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun i _ m => Nat.lor m (Nat.shiftLeft 1 i)) l

@[expose] def meetN (a b : Nat) : Bool := Nat.blt 0 (Nat.land a b)

@[expose] noncomputable def symOk : Bool :=
  (List.range 72).all fun i => (List.range 72).all fun j => bitN (nthN adjT i) j == bitN (nthN adjT j) i

@[expose] noncomputable def rowsOk : Bool :=
  adjT.length == 72 && adjT.all (fun r => Nat.blt r 4722366482869645213696) && roots.length == 72

@[expose] noncomputable def strictL (y : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def strictBo (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

theorem strictL_eq (y : Nat) (k : Nat → List Nat) : strictL y k = k y := by cases y <;> rfl

theorem strictBo_eq (y : Nat) (k : Nat → Bool) : strictBo y k = k y := by cases y <;> rfl

@[expose] noncomputable def stepLM (pm seen : List Nat) : List Nat :=
  strictL (mOf seen) fun m => seen ++ pm.filter (fun j => !bitN m j && meetN m (nthN adjT j))

@[expose] noncomputable def iterStepM (pm : List Nat) : Nat → List Nat → List Nat
  | 0, seen => seen
  | k + 1, seen =>
    let next := stepLM pm seen
    if next.length == seen.length then seen else iterStepM pm k next

@[expose] noncomputable def compOfM (pm : List Nat) (seed : Nat) : List Nat := iterStepM pm 72 [seed]

@[expose] noncomputable def closedInM (pm c : List Nat) : Bool :=
  strictBo (mOf c) fun m => pm.all (fun j => bitN m j || !meetN m (nthN adjT j))

@[expose] noncomputable def goodAtM (t : Nat) : Bool :=
  let pm := phiLK t
  let q := qOf (repL t)
  let ps := pm.map (fun i => (i, compOfM pm i))
  ps.all (fun p => closedInM pm p.2) &&
    (if q == 0 then ps.all (fun p => p.2.length ≤ 6)
     else
      ps.all (fun p => p.2.length ≤ 6 ||
          strictBo (mOf p.2) fun m => ps.all (fun r => r.2.length ≤ 6 || bitN m r.1)) &&
        ps.any (fun p => p.2.length == (if q == 1 then 24 else 30) && kerSizeK p.2 == 3))

@[expose] noncomputable def checkM : Bool :=
  rootsOk () && radOk () && (List.range 243).all (fun t => t == 0 || goodAtM t) &&
    cntQ 0 == 80 && cntQ 1 == 90 && cntQ 2 == 72

theorem meetN_iff (a b : Nat) : meetN a b = true ↔ ∃ i, a.testBit i = true ∧ b.testBit i = true := by
  unfold meetN
  rw [Nat.blt_eq]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero (Nat.pos_iff_ne_zero.1 h)
    change (a &&& b).testBit i = true at hi
    rw [Nat.testBit_and, Bool.and_eq_true] at hi
    exact ⟨i, hi⟩
  · rintro ⟨i, ha, hb⟩
    refine Nat.pos_iff_ne_zero.2 fun h0 => ?_
    have e : (a &&& b).testBit i = true := by rw [Nat.testBit_and, ha, hb]; rfl
    change (Nat.land a b).testBit i = true at e
    rw [h0, Nat.zero_testBit] at e
    exact Bool.noConfusion e

theorem bitN_eq (m j : Nat) : bitN m j = m.testBit j := by
  have e : bitN m j = meetN m (1 <<< j) := rfl
  rw [Bool.eq_iff_iff, e, meetN_iff]
  constructor
  · rintro ⟨i, hm, hi⟩
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq] at hi
    rw [hi]
    exact hm
  · intro h
    refine ⟨j, h, ?_⟩
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq]

theorem testBit_mOf (l : List Nat) (j : Nat) : (mOf l).testBit j = l.contains j := by
  induction l with
  | nil => exact Nat.zero_testBit j
  | cons i l ih =>
    change ((mOf l) ||| (1 <<< i)).testBit j = (i :: l).contains j
    rw [Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow, List.contains_cons]
    by_cases h : i = j
    · subst h
      simp
    · have h' : (j == i) = false := beq_false_of_ne (Ne.symm h)
      rw [decide_eq_false h, h', Bool.false_or, Bool.or_false]

theorem nthN_ge : ∀ (P : List Nat) (j : Nat), P.length ≤ j → nthN P j = 0
  | [], _, _ => rfl
  | _ :: _, 0, h => absurd h (by simp)
  | _ :: P, j + 1, h => nthN_ge P j (by simp at h; omega)

theorem nthN_mem : ∀ (P : List Nat) (j : Nat), j < P.length → nthN P j ∈ P
  | [], _, h => absurd h (by simp)
  | _ :: _, 0, _ => List.mem_cons_self
  | _ :: P, j + 1, h => List.mem_cons_of_mem _ (nthN_mem P j (by simp at h; omega))

theorem getD_nil_of_le (l : List (List Int)) (i : Nat) (h : l.length ≤ i) : l.getD i [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

theorem pairZ_nil_left (b : List Int) : pairZ [] b = 0 := by
  simp [pairZ, idx6]

theorem pairZ_nil_right (a : List Int) : pairZ a [] = 0 := by
  simp [pairZ, idx6]

section

variable (hA : adjOk = true) (hS : symOk = true) (hR : rowsOk = true)

include hA hS hR in
theorem adjK_eq (i j : Nat) : adjK i j = (nthN adjT j).testBit i := by
  simp only [rowsOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Nat.blt_eq] at hR
  obtain ⟨⟨hl, hlt⟩, hr⟩ := hR
  rw [← adjB_eq hA]
  by_cases hj : j < 72
  · by_cases hi : i < 72
    · rw [adjB_eq hA]
      unfold adjK
      have hc : (Nat.blt i 72 && Nat.blt j 72) = true := by
        rw [Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq]
        exact ⟨hi, hj⟩
      rw [hc]
      have h1 := List.all_eq_true.1 hS i (List.mem_range.2 hi)
      have h2 := List.all_eq_true.1 h1 j (List.mem_range.2 hj)
      rw [beq_iff_eq] at h2
      change bitN (nthN adjT i) j = _
      rw [h2, bitN_eq]
    · have hroot : rootAt i = [] := getD_nil_of_le roots i (by omega)
      have hrow : nthN adjT j < 2 ^ i := by
        have := hlt _ (nthN_mem adjT j (by omega))
        calc nthN adjT j < 4722366482869645213696 := this
          _ = 2 ^ 72 := by decide
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow hrow]
      simp [adjB, hroot, pairZ_nil_left]
  · rw [nthN_ge adjT j (by omega), Nat.zero_testBit]
    have hroot : rootAt j = [] := getD_nil_of_le roots j (by omega)
    simp [adjB, hroot, pairZ_nil_right]

include hA hS hR in
theorem any_adjK (seen : List Nat) (j : Nat) :
    (seen.any fun i => adjK i j) = meetN (mOf seen) (nthN adjT j) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, meetN_iff]
  constructor
  · rintro ⟨i, hi, ha⟩
    refine ⟨i, ?_, ?_⟩
    · rw [testBit_mOf]
      exact List.contains_iff_mem.2 hi
    · rw [← adjK_eq hA hS hR]
      exact ha
  · rintro ⟨i, hm, hr⟩
    rw [testBit_mOf] at hm
    exact ⟨i, List.contains_iff_mem.1 hm, (adjK_eq hA hS hR i j).trans hr⟩

include hA hS hR in
theorem iterStep_eqM (pm : List Nat) : ∀ k seen, iterStepK pm k seen = iterStepM pm k seen
  | 0, _ => rfl
  | k + 1, seen => by
    have e : stepLK pm seen = stepLM pm seen := by
      simp only [stepLK, stepLM, strictL_eq, any_adjK hA hS hR, bitN_eq, testBit_mOf]
    simp only [iterStepK, iterStepM, e, iterStep_eqM pm k]

include hA hS hR in
theorem goodAt_eqM (t : Nat) : goodAtK t = goodAtM t := by
  have hc : ∀ pm i, compOfK pm i = compOfM pm i := fun pm i => iterStep_eqM hA hS hR pm 72 [i]
  have hcl : ∀ pm c, closedInK pm c = closedInM pm c := fun pm c => by
    simp only [closedInK, closedInM, strictBo_eq, any_adjK hA hS hR, bitN_eq, testBit_mOf]
  simp only [goodAtK, goodAtM, hc, hcl, strictBo_eq, bitN_eq, testBit_mOf]

include hA hS hR in
theorem checkK_eq : checkK = checkM := by
  simp only [checkK, checkM, goodAt_eqM hA hS hR]

end

end CertificateChecks.E6HeartK
