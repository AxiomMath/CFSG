module

public import Certificates.Data.Kernel.L5.EngRec

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.Fus

open CFSG.GH74.GLS.C3.Layer2

variable {n : Nat}

@[expose] def parW (v : List Bool) (w : List Nat) : Bool :=
  w.foldl (fun acc i => xor acc (v.getD i false)) false

@[expose] def chiMask (v : List Bool) : List (List Nat) → Nat
  | [] => 0
  | w :: l => (parW v w).toNat + 2 * chiMask v l

theorem testBit_chiMask (v : List Bool) : ∀ (l : List (List Nat)) (j : Nat),
    (chiMask v l).testBit j = parW v (l.getD j [])
  | [], j => by simp [chiMask, parW]
  | w :: l, j => by
    have hb := Bool.toNat_le (parW v w)
    cases j with
    | zero =>
      rw [List.getD_cons_zero, chiMask, Nat.testBit_zero]
      have e : ((parW v w).toNat + 2 * chiMask v l) % 2 = (parW v w).toNat := by omega
      rw [e]
      cases parW v w <;> rfl
    | succ j =>
      rw [List.getD_cons_succ, chiMask, Nat.testBit_succ, ← testBit_chiMask v l j]
      have e : ((parW v w).toNat + 2 * chiMask v l) / 2 = chiMask v l := by omega
      rw [e]

theorem getD_toList' {β : Type} (A : Array β) (i : Nat) (d : β) :
    A.getD i d = A.toList.getD i d := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

variable [Group (Idx n)]

theorem chiV_eq_testBit (wordA : Array (List Nat)) (v : List Bool) (m : Idx n) :
    chiV wordA v m = (chiMask v wordA.toList).testBit m.v := by
  rw [testBit_chiMask, ← getD_toList']
  rfl

@[expose] def charValidM (mgens : List (Idx n)) (M : Nat) (v : List Bool) : Bool :=
  !(M.testBit (1 : Idx n).v) && (elemsI n).all fun m => (List.range mgens.length).all fun i =>
    decide (M.testBit (m * mgens.getD i 1).v = xor (M.testBit m.v) (v.getD i false))

@[expose] def maxSubsM (mgens : List (Idx n)) (wordA : Array (List Nat)) : List (Array Bool) :=
  ((allVecs mgens.length).filter fun v => charValidM mgens (chiMask v wordA.toList) v).map
    fun v => ((elemsI n).map fun m => !((chiMask v wordA.toList).testBit m.v)).toArray

@[expose] def mgChkM (mg : List (Idx n)) (ms : List (Array Bool)) : Bool :=
  decide ((maxSubsM mg (wordArrOf mg)).map Array.toList = ms.map Array.toList) &&
    (elemsI n).all fun m => decide (evW mg ((wordArrOf mg).getD m.v []) = m)

theorem charValid_eq_M (mgens : List (Idx n)) (wordA : Array (List Nat)) (v : List Bool) :
    charValid mgens wordA v = charValidM mgens (chiMask v wordA.toList) v := by
  unfold charValid charValidM
  simp only [chiV_eq_testBit]

theorem charValid_eq_fun (mgens : List (Idx n)) (wordA : Array (List Nat)) :
    charValid mgens wordA = fun v => charValidM mgens (chiMask v wordA.toList) v :=
  funext (charValid_eq_M mgens wordA)

theorem maxSubsOf_eq_M (mgens : List (Idx n)) (wordA : Array (List Nat)) :
    maxSubsOf mgens wordA = maxSubsM mgens wordA := by
  unfold maxSubsOf maxSubsM
  simp only [charValid_eq_fun, chiV_eq_testBit]

theorem decide_arrs_eq (L M : List (Array Bool)) :
    decide (L = M) = decide (L.map Array.toList = M.map Array.toList) := by
  have hiff : L = M ↔ L.map Array.toList = M.map Array.toList :=
    ⟨fun h => by rw [h], fun h => List.map_injective_iff.2 (fun _ _ hab => Array.ext' hab) h⟩
  by_cases h : L = M
  · rw [decide_eq_true h, decide_eq_true (hiff.1 h)]
  · rw [decide_eq_false h, decide_eq_false (fun h' => h (hiff.2 h'))]

theorem mgChk_eq_M (mg : List (Idx n)) (ms : List (Array Bool)) : mgChk mg ms = mgChkM mg ms := by
  unfold mgChk mgChkM
  simp only [maxSubsOf_eq_M, decide_arrs_eq]

end CFSG.GH74.GLS.C3.Layer2.L5.Fus

end
