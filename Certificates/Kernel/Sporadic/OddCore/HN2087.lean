module

public import CFSG.Sporadic.HNOddCore.NatCheckInputs
public import CFSG.Certificates.Kernel.Spor.PWord
public import CFSG.Sporadic.Schreier.ONPermArr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
public import Mathlib.Data.Vector.Basic
public import Mathlib.GroupTheory.Perm.Basic

public section

namespace CertificateChecks.KernelSpor.HN2087

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore.Native
open CFSG.Sporadic.HNSchreier.Native CFSG.KS.PW CFSG.KS.TW

@[expose] def natInv : Array (List Nat) :=
  #[[6, 3, 4, 1, 2, 8, 0, 11, 5, 10, 9, 7], [8, 6, 2, 11, 3, 9, 1, 4, 0, 5, 10, 7],
    [0, 1, 2, 7, 11, 5, 6, 3, 8, 9, 10, 4], [0, 11, 7, 3, 4, 5, 6, 2, 8, 9, 10, 1],
    [0, 1, 4, 3, 2, 5, 7, 6, 8, 9, 10, 11], [0, 1, 6, 3, 7, 5, 2, 4, 8, 9, 10, 11],
    [0, 4, 2, 3, 1, 5, 11, 7, 8, 9, 10, 6], [0, 5, 7, 3, 10, 1, 6, 8, 2, 4, 11, 9],
    [0, 1, 2, 3, 4, 9, 6, 8, 7, 5, 10, 11], [0, 1, 2, 3, 4, 5, 8, 6, 7, 9, 10, 11],
    [0, 1, 2, 3, 8, 5, 6, 4, 7, 9, 10, 11], [0, 1, 2, 3, 4, 5, 6, 8, 10, 9, 7, 11],
    [0, 1, 2, 3, 4, 10, 9, 7, 8, 6, 5, 11], [0, 1, 2, 3, 4, 5, 6, 7, 10, 8, 9, 11],
    [0, 1, 2, 3, 8, 5, 6, 11, 7, 10, 9, 4], [0, 1, 2, 3, 4, 5, 6, 7, 11, 10, 9, 8],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 9, 10]]

@[expose] def natF (j x : Nat) : Nat := (LocalData.strongImages.getD j []).getD x 0

@[expose] def natFI (j x : Nat) : Nat := (natInv.getD j []).getD x 0

@[expose] def nOrig : Array (Array Nat) := #[natArr LocalData.natGen1, natArr LocalData.natGen2]

@[expose] def nS : Array (Array Nat) := extendStrong 12 nOrig LocalData.strongWords

theorem hO : ∀ j < 2, nOrig[j]! = Array.ofFn (n := 12) fun i => natF j i.val := by
  intro j hj
  apply arr_ext (by interval_cases j <;> decide)
  intro x hx
  interval_cases j <;> interval_cases x <;> decide

theorem hW : ∀ j, 2 ≤ j → j < 17 → (∀ l ∈ LocalData.strongWords[j]!, l ≠ 0 ∧ l.natAbs ≤ j) ∧
    ∀ x < 12, natF j x = LocalData.strongWords[j]!.foldr (GZ natF natFI) x := by
  intro j h2 h17
  interval_cases j <;> refine ⟨by decide, fun x hx => ?_⟩ <;> interval_cases x <;> decide

theorem hinv : ∀ j < 17, ∀ x < 12, natF j x < 12 ∧ natFI j x < 12 ∧ natFI j (natF j x) = x := by
  intro j hj x hx
  interval_cases j <;> interval_cases x <;> decide

theorem nS_get : nS.size = 17 ∧ ∀ j < 17, nS[j]! = Array.ofFn (n := 12) fun i => natF j i.val :=
  extendStrong_get (n := 12) (m := 2) (s := 17) (orig := nOrig) (W := LocalData.strongWords)
    (by decide) (by decide) (by norm_num) hO hW hinv

theorem natLetters : LettersOK 12 17 nS (pinvs 12 nS) natF natFI := by
  intro j hj x hx
  have e := nS_get.2 j hj
  refine ⟨by rw [e, ofFn_get' hx], ?_, (hinv j hj x hx).1, (hinv j hj x hx).2.1⟩
  unfold pinvs
  rw [getElem!_pos _ j (by simpa [nS_get.1] using hj), Array.getElem_map,
    ← getElem!_pos nS j (by simpa [nS_get.1] using hj), e]
  exact CFSG.KS.CB.pinvCand_get (fun y hy => (hinv j hj y hy).1)
    (fun y hy => (hinv j hj y hy).2.2) hx

@[expose] noncomputable def natK (w : List Int) (a : Nat → Nat) : Bool :=
  plettersOK 17 w && (List.range 12).all fun x => w.foldr (GZ natF natFI) x == a x

theorem natOK_of {w : List Int} {a : Array Nat} (h : natK w (fun x => a[x]!) = true) :
    natOK nS (pinvs 12 nS) w a = true := by
  simp only [natK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨hl, hp⟩ := h
  have hl' : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 17 := by
    simpa [plettersOK, List.all_eq_true] using hl
  simp only [natOK, hl, Bool.true_and, peq]
  rw [allBelowN_iff]
  intro x hx
  rw [(pword_get natLetters w hl' x hx).1, hp x hx, beq_self_eq_true]

theorem natAllOK_of {W : Array (List Int)} {A : Array (List Nat)} (hs : W.size = A.size)
    (h : ∀ j < W.size, natK W[j]! (fun x => (natArr A[j]!)[x]!) = true) :
    natAllOK nS (pinvs 12 nS) W A = true := by
  simp only [natAllOK, hs, beq_self_eq_true, Bool.true_and]
  rw [allBelowN_iff]
  intro j hj
  exact natOK_of (h j (by rw [hs]; exact hj))

@[expose] def cycF (i x : Nat) : Nat :=
  if x = 4 then 5 else if x = 5 then i else if x = i then 4 else x

theorem cyc45_get (i : Nat) :
    (fun x => (cyc45 i)[x]!) = fun x => if x < 12 then cycF i x else 0 := by
  funext x
  by_cases hx : x < 12
  · simp only [hx, ↓reduceIte]
    rw [cyc45, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]
    simp [cycF]
  · simp only [hx, ↓reduceIte]
    rw [getElem!_neg _ x (by simpa [cyc45] using hx)]
    rfl

theorem natChecks_eq : natChecks = true := by
  unfold natChecks
  change natChecksS nS = true
  unfold natChecksS
  simp only [Bool.and_eq_true, beq_iff_eq]
  and_intros
  · exact natOK_of (by decide)
  · exact natOK_of (by decide)
  · refine natAllOK_of (by decide) fun j hj => ?_
    change j < 9 at hj
    interval_cases j <;> decide
  · decide
  · refine natAllOK_of (by decide) fun j hj => ?_
    change j < 9 at hj
    interval_cases j <;> decide
  · decide
  · refine natAllOK_of (by decide) fun j hj => ?_
    change j < 10 at hj
    interval_cases j <;> decide
  · decide
  · decide
  · rw [allBelowN_iff]
    intro j hj
    refine natOK_of ?_
    rw [cyc45_get]
    interval_cases j <;> decide

theorem commOK_of {a b : Array Nat}
    (h : (List.range 12).all (fun x => a[b[x]!]! == b[a[x]!]!) = true) : commOK a b = true := by
  simp only [List.all_eq_true, List.mem_range] at h
  unfold commOK peq
  rw [allBelowN_iff]
  intro x hx
  rw [pcomp_get' hx, pcomp_get' hx]
  exact h x hx

theorem natCommChecks_eq : natCommChecks = true := by
  unfold natCommChecks
  simp only [Bool.and_eq_true]
  and_intros
  · rw [allBelowN_iff]
    intro j hj
    change j < 9 at hj
    interval_cases j <;> exact commOK_of (by decide)
  · rw [allBelowN_iff]
    intro j hj
    change j < 9 at hj
    interval_cases j <;> exact commOK_of (by decide)
  · rw [allBelowN_iff]
    intro j hj
    change j < 10 at hj
    interval_cases j <;> exact commOK_of (by decide)
  · exact commOK_of (by decide)

theorem facts2087 : natChecks = true ∧ natCommChecks = true := ⟨natChecks_eq, natCommChecks_eq⟩

end CertificateChecks.KernelSpor.HN2087

end
