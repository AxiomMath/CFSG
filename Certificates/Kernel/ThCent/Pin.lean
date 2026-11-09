module

public import Certificates.Data.Kernel.ThCent.Pin
public import Certificates.Kernel.ThCent.Data
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.ThThreeInputs
import Certificates.Kernel.ThCent.L7Pin
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.Common.Eval
meta import Certificates.Data.CFSGNative.Timmesfeld.ThCent

namespace CFSG.KD.ThCent.Pin

open Lean CFSG.KC.Eval

meta def mulW (c rm A B : Nat) : Nat := Id.run do
  let mut acc := 0
  for k in [0:248] do
    acc := Nat.xor acc (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A k) c) rm)
      (Nat.mul (Nat.land (Nat.shiftRight B (k * 256)) rm) c))
  return acc

meta def wordSnap (c rm one a b : Nat) (s : String) (k : Nat) : Array Val := Id.run do
  let mut acc := one
  let mut out : Array Val := #[]
  let mut n := 0
  for ch in s.toList do
    acc := mulW c rm acc (if ch == 'a' then a else b)
    n := n + 1
    if n % k == 0 then out := out.push (.nat acc)
  if n % k != 0 then out := out.push (.nat acc)
  return out

meta def wordStep : Step := fun args => do
  let #[.nat c, .nat rm, .nat one, .nat a, .nat b, .nat k] := args
    | throw "wordStep: expected c rm ONE A B k"
  let named (p : String) (xs : Array Val) : Array (Name × Val) :=
    (xs.mapIdx fun i v => (Name.mkSimple s!"{p}{i}", v)).push
      (Name.mkSimple s!"{p}L", .list (xs.mapIdx fun i _ => .ref (Name.mkSimple s!"{p}{i}")))
  return named "A" (wordSnap c rm one a b CFSG.Sporadic.Th.Native.x1Str k) ++
    named "B" (wordSnap c rm one a b CFSG.Sporadic.Th.Native.x2Str k)

#kc_eval CFSG.KD.ThCent.Pin XW CFSG.KD.ThCent.Pin.wordStep CFSG.KD.ThS.c CFSG.KD.ThS.rm
  CFSG.KD.ThS.ONE CFSG.KD.ThS.Rf_1 CFSG.KD.ThS.Rf_2 45

end CFSG.KD.ThCent.Pin

public section

namespace CFSG.KD.ThCent.Pin

open CFSG.KC.Th CFSG.KC.ThCent CFSG.SectionRank.Native CFSG.Sporadic.Th.Native

theorem a2 : Nat.beq (mulB ThS.c ThS.rm (ThS.RBf 1) (ThS.RBf 1)) ThS.ONE = true := by
  quickRfl

theorem strictF_eqW {α : Sort _} (y : Nat) (k : Nat → α) : strictF y k = k y := by
  cases y <;> rfl

theorem wordFrom_consW (c rm A B Bi : Nat) (l : Int) (w : List Int) (acc : Nat) :
    wordFrom c rm A B Bi (l :: w) acc = wordFrom c rm A B Bi w (mulB c rm acc (letZ A B Bi l)) :=
  strictF_eqW (mulB c rm acc (letZ A B Bi l)) (wordFrom c rm A B Bi w)

theorem wordFrom_appendW (c rm A B Bi : Nat) (p q : List Int) (acc : Nat) :
    wordFrom c rm A B Bi (p ++ q) acc = wordFrom c rm A B Bi q (wordFrom c rm A B Bi p acc) := by
  induction p generalizing acc with
  | nil => rfl
  | cons l p ih => rw [List.cons_append, wordFrom_consW, wordFrom_consW, ih]

@[expose] def wsegW (w : List Int) (i : Nat) : List Int := (w.drop (i * 45)).take 45

theorem wordZ_segsW (c rm ONE A B Bi : Nat) (w : List Int) (S : Nat → Nat) (m : Nat)
    (h0 : S 0 = ONE) (hm : w.length ≤ m * 45)
    (hs : ∀ i < m, Nat.beq (wordFrom c rm A B Bi (wsegW w i) (S i)) (S (i + 1)) = true) :
    wordZ c rm ONE A B Bi w = S m := by
  rw [wordZ, ← h0]
  have key : ∀ j ≤ m, wordFrom c rm A B Bi (w.take (j * 45)) (S 0) = S j := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [Nat.succ_mul, List.take_add, wordFrom_appendW, ih (by omega)]
      exact Nat.eq_of_beq_eq_true (hs j (by omega))
  rw [← List.take_of_length_le hm]
  exact key m (Nat.le_refl m)

@[expose] noncomputable def snapA (i : Nat) : Nat := (ThS.ONE :: XW.AL).getD i 0

@[expose] noncomputable def snapB (i : Nat) : Nat := (ThS.ONE :: XW.BL).getD i 0

theorem segA_0 : Nat.beq (wordFrom ThS.c ThS.rm (ThS.RBf 1) (ThS.RBf 2) ThS.Bi
    (wsegW (abWord x1Str) 0) (snapA 0)) (snapA (0 + 1)) = true := by quickRfl
theorem segA_1 : Nat.beq (wordFrom ThS.c ThS.rm (ThS.RBf 1) (ThS.RBf 2) ThS.Bi
    (wsegW (abWord x1Str) 1) (snapA 1)) (snapA (1 + 1)) = true := by quickRfl

theorem segB_0 : Nat.beq (wordFrom ThS.c ThS.rm (ThS.RBf 1) (ThS.RBf 2) ThS.Bi
    (wsegW (abWord x2Str) 0) (snapB 0)) (snapB (0 + 1)) = true := by quickRfl
theorem segB_1 : Nat.beq (wordFrom ThS.c ThS.rm (ThS.RBf 1) (ThS.RBf 2) ThS.Bi
    (wsegW (abWord x2Str) 1) (snapB 1)) (snapB (1 + 1)) = true := by quickRfl
theorem segB_2 : Nat.beq (wordFrom ThS.c ThS.rm (ThS.RBf 1) (ThS.RBf 2) ThS.Bi
    (wsegW (abWord x2Str) 2) (snapB 2)) (snapB (2 + 1)) = true := by quickRfl
theorem segB_3 : Nat.beq (wordFrom ThS.c ThS.rm (ThS.RBf 1) (ThS.RBf 2) ThS.Bi
    (wsegW (abWord x2Str) 3) (snapB 3)) (snapB (3 + 1)) = true := by quickRfl
theorem len_x1 : (abWord x1Str).length ≤ 2 * 45 := by decide +kernel
theorem len_x2 : (abWord x2Str).length ≤ 4 * 45 := by decide +kernel

theorem wordZ_x1 :
    wordZ ThS.c ThS.rm ThS.ONE (ThS.RBf 1) (ThS.RBf 2) ThS.Bi (abWord x1Str) = snapA 2 := by
  refine wordZ_segsW ThS.c ThS.rm ThS.ONE (ThS.RBf 1) (ThS.RBf 2) ThS.Bi (abWord x1Str) snapA 2
    rfl len_x1 fun i hi => ?_
  match i, hi with
  | 0, _ => exact segA_0
  | 1, _ => exact segA_1

theorem wordZ_x2 :
    wordZ ThS.c ThS.rm ThS.ONE (ThS.RBf 1) (ThS.RBf 2) ThS.Bi (abWord x2Str) = snapB 4 := by
  refine wordZ_segsW ThS.c ThS.rm ThS.ONE (ThS.RBf 1) (ThS.RBf 2) ThS.Bi (abWord x2Str) snapB 4
    rfl len_x2 fun i hi => ?_
  match i, hi with
  | 0, _ => exact segB_0
  | 1, _ => exact segB_1
  | 2, _ => exact segB_2
  | 3, _ => exact segB_3

theorem z3B : strictF (mulB ThS.c ThS.rm
    (wordZ ThS.c ThS.rm ThS.ONE (ThS.RBf 1) (ThS.RBf 2) ThS.Bi (abWord x1Str))
    (wordZ ThS.c ThS.rm ThS.ONE (ThS.RBf 1) (ThS.RBf 2) ThS.Bi (abWord x2Str)))
      (fun M => Nat.beq (BigS.powB ThS.c ThS.rm ThS.ONE M 9 4) W.Z3B) = true := by
  rw [wordZ_x1, wordZ_x2]
  quickRfl

theorem s3A : Nat.beq (runPk ThS.c ThS.rm ThS.ONE
    CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative.prog3
    (initPk (ThS.RBf 1) (ThS.RBf 2) ThS.ONE) 11) W.Z3A = true := by
  quickRfl

theorem z7 : Nat.beq (runPk ThS.c ThS.rm ThS.ONE
    (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative.prog7 ++
      [.pow 6 25 43, .mul 24 43 44])
    (initPk (ThS.RBf 1) (ThS.RBf 2) ThS.ONE) 44) W.Z7 = true := by
  rw [L.runPk_append7, L.run7]
  quickRfl

theorem neg_s3A : BigS.notB (Nat.beq (runPk ThS.c ThS.rm ThS.ONE
    CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative.prog3
    (initPk (ThS.RBf 1) (ThS.RBf 2) ThS.ONE) 12) W.Z3A) = true := by
  quickRfl

theorem neg_z3B : BigS.notB (strictF (mulB ThS.c ThS.rm
    (wordZ ThS.c ThS.rm ThS.ONE (ThS.RBf 1) (ThS.RBf 2) ThS.Bi (abWord x2Str))
    (wordZ ThS.c ThS.rm ThS.ONE (ThS.RBf 1) (ThS.RBf 2) ThS.Bi (abWord x1Str)))
      (fun M => Nat.beq (BigS.powB ThS.c ThS.rm ThS.ONE M 3 4) W.Z3B)) = true := by
  rw [wordZ_x1, wordZ_x2]
  quickRfl

end CFSG.KD.ThCent.Pin

end
