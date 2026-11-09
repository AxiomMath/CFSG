module

public import Certificates.Kernel.J4Fam.Data
public import Certificates.Data.Kernel.J4Fam
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Fam

open CFSG.KC.J4Fam
open CFSG.KC (notB)

theorem lv0_ok' : (LV0 == [0]) = true := by quickRfl

theorem lv7_nil' : LV7.isEmpty = true := by quickRfl

theorem lv0_ok : LV0 = [0] := beq_iff_eq.mp lv0_ok'

theorem lv7_nil : LV7 = [] := List.isEmpty_iff.mp lv7_nil'

theorem lens_lv : (LV0.length == 1 && LV1.length == 191 && LV2.length == 2091 &&
    LV3.length == 3643 && LV4.length == 1449 && LV5.length == 130 && LV6.length == 2) = true := by
  quickRfl

theorem tg_ok : (TG0.length == LV0.length && TG1.length == LV1.length && TG2.length == LV2.length &&
    TG3.length == LV3.length && TG4.length == LV4.length && TG5.length == LV5.length &&
    TG6.length == LV6.length) = true := by quickRfl

@[expose] noncomputable def orRK (l : List Nat) (b : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) b (fun t _ ih => Nat.lor ih (Nat.shiftLeft 1 t)) l

@[expose] noncomputable def coverRK (TG : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun l _ ih => orRK l ih) TG

theorem orRK_or : ∀ (l : List Nat) (a x : Nat), orRK l (a ||| x) = orRK l a ||| x
  | [], _, _ => rfl
  | t :: l, a, x => by
    change orRK l (a ||| x) ||| 1 <<< t = (orRK l a ||| 1 <<< t) ||| x
    rw [orRK_or l a x, Nat.or_assoc, Nat.or_comm x, ← Nat.or_assoc]

theorem foldl_orRK : ∀ (l : List Nat) (a : Nat), l.foldl (fun a s => a ||| (1 <<< s)) a = orRK l a
  | [], _ => rfl
  | t :: l, a => by
    rw [List.foldl_cons, foldl_orRK l, orRK_or]
    rfl

theorem foldl_coverRK : ∀ (TG : List (List Nat)) (a : Nat),
    TG.foldl (fun acc l => l.foldl (fun a s => a ||| (1 <<< s)) acc) a = a ||| coverRK TG
  | [], a => (Nat.or_zero a).symm
  | l :: TG, a => by
    rw [List.foldl_cons, foldl_coverRK TG, foldl_orRK]
    change orRK l a ||| coverRK TG = a ||| orRK l (coverRK TG)
    have e1 := orRK_or l 0 a
    have e2 := orRK_or l 0 (coverRK TG)
    rw [Nat.zero_or] at e1 e2
    rw [e1, e2, Nat.or_comm (orRK l 0) a, Nat.or_assoc, Nat.or_comm (orRK l 0), ← Nat.or_assoc]

theorem coverOK_of_RK {N : Nat} {TG : List (List Nat)}
    (h : Nat.beq (Nat.land (coverRK TG) (2 ^ N - 1)) (2 ^ N - 1) = true) : coverOK N TG = true := by
  rw [coverOK.eq_1, foldl_coverRK, Nat.zero_or, beq_iff_eq]
  exact Nat.eq_of_beq_eq_true h

theorem cv0K : Nat.beq (Nat.land (coverRK TG0) (2 ^ LV1.length - 1)) (2 ^ LV1.length - 1) = true := by
  quickRfl
theorem cv1K : Nat.beq (Nat.land (coverRK TG1) (2 ^ LV2.length - 1)) (2 ^ LV2.length - 1) = true := by
  quickRfl
theorem cv2K : Nat.beq (Nat.land (coverRK TG2) (2 ^ LV3.length - 1)) (2 ^ LV3.length - 1) = true := by
  quickRfl
theorem cv3K : Nat.beq (Nat.land (coverRK TG3) (2 ^ LV4.length - 1)) (2 ^ LV4.length - 1) = true := by
  quickRfl
theorem cv4K : Nat.beq (Nat.land (coverRK TG4) (2 ^ LV5.length - 1)) (2 ^ LV5.length - 1) = true := by
  quickRfl
theorem cv5K : Nat.beq (Nat.land (coverRK TG5) (2 ^ LV6.length - 1)) (2 ^ LV6.length - 1) = true := by
  quickRfl
theorem cv6K : Nat.beq (Nat.land (coverRK TG6) (2 ^ LV7.length - 1)) (2 ^ LV7.length - 1) = true := by
  quickRfl

theorem cv_ok0 : coverOK LV1.length TG0 = true := coverOK_of_RK cv0K
theorem cv_ok1 : coverOK LV2.length TG1 = true := coverOK_of_RK cv1K
theorem cv_ok2 : coverOK LV3.length TG2 = true := coverOK_of_RK cv2K
theorem cv_ok3 : coverOK LV4.length TG3 = true := coverOK_of_RK cv3K
theorem cv_ok4 : coverOK LV5.length TG4 = true := coverOK_of_RK cv4K
theorem cv_ok5 : coverOK LV6.length TG5 = true := coverOK_of_RK cv5K
theorem cv_ok6 : coverOK LV7.length TG6 = true := coverOK_of_RK cv6K

@[expose] noncomputable def eqWL {α : Type} (e : α → α → Bool) (a : List α) : List α → Bool :=
  List.rec (motive := fun _ => List α → Bool)
    (fun b => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) b)
    (fun x _ ih b => List.rec (motive := fun _ => Bool) false
      (fun y ys _ => Bool.rec false (ih ys) (e x y)) b) a

theorem eqWL_eq {α : Type} {e : α → α → Bool} (he : ∀ x y, e x y = true → x = y) :
    ∀ {a b : List α}, eqWL e a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | x :: a, y :: b, h => by
    change Bool.rec false (eqWL e a b) (e x y) = true at h
    cases hxy : e x y
    · rw [hxy] at h
      exact Bool.noConfusion h
    · rw [hxy] at h
      rw [he x y hxy, eqWL_eq he h]

theorem treeOK_of_eqWL {α : Type} [BEq α] [LawfulBEq α] {e : α → α → Bool}
    (he : ∀ x y, e x y = true → x = y) {T : List (List (List α))} {l : List α}
    (h : eqWL (eqWL (eqWL e)) T (chunks l.length (chunks l.length l)) = true) :
    treeOK T l = true := by
  have h3 : ∀ x y, eqWL (eqWL e) x y = true → x = y := fun _ _ => eqWL_eq fun _ _ => eqWL_eq he
  rw [treeOK.eq_1, eqWL_eq h3 h]
  exact beq_self_eq_true _

theorem eqWL_nat : ∀ x y : List Nat, eqWL Nat.beq x y = true → x = y :=
  fun _ _ => eqWL_eq fun _ _ => Nat.eq_of_beq_eq_true

theorem tr0K : eqWL (eqWL (eqWL Nat.beq)) LVT0 (chunks LV0.length (chunks LV0.length LV0)) = true := by
  quickRfl
theorem tr1K : eqWL (eqWL (eqWL Nat.beq)) LVT1 (chunks LV1.length (chunks LV1.length LV1)) = true := by
  quickRfl
theorem tr2K : eqWL (eqWL (eqWL Nat.beq)) LVT2 (chunks LV2.length (chunks LV2.length LV2)) = true := by
  quickRfl
theorem tr3K : eqWL (eqWL (eqWL Nat.beq)) LVT3 (chunks LV3.length (chunks LV3.length LV3)) = true := by
  quickRfl
theorem tr4K : eqWL (eqWL (eqWL Nat.beq)) LVT4 (chunks LV4.length (chunks LV4.length LV4)) = true := by
  quickRfl
theorem tr5K : eqWL (eqWL (eqWL Nat.beq)) LVT5 (chunks LV5.length (chunks LV5.length LV5)) = true := by
  quickRfl
theorem tr6K : eqWL (eqWL (eqWL Nat.beq)) LVT6 (chunks LV6.length (chunks LV6.length LV6)) = true := by
  quickRfl
theorem tr7K : eqWL (eqWL (eqWL Nat.beq)) LVT7 (chunks LV7.length (chunks LV7.length LV7)) = true := by
  quickRfl
theorem trFBK : eqWL (eqWL (eqWL Nat.beq)) FBT (chunks FB.length (chunks FB.length FB)) = true := by
  quickRfl
theorem trFLLK : eqWL (eqWL (eqWL (eqWL Nat.beq))) FLLT
    (chunks FLL.length (chunks FLL.length FLL)) = true := by
  quickRfl

theorem tr_ok : (treeOK LVT0 LV0 && treeOK LVT1 LV1 && treeOK LVT2 LV2 && treeOK LVT3 LV3 &&
    treeOK LVT4 LV4 && treeOK LVT5 LV5 && treeOK LVT6 LV6 && treeOK LVT7 LV7 && treeOK FBT FB &&
    treeOK FLLT FLL) = true := by
  rw [treeOK_of_eqWL (fun _ _ => Nat.eq_of_beq_eq_true) tr0K,
    treeOK_of_eqWL (fun _ _ => Nat.eq_of_beq_eq_true) tr1K,
    treeOK_of_eqWL (fun _ _ => Nat.eq_of_beq_eq_true) tr2K,
    treeOK_of_eqWL (fun _ _ => Nat.eq_of_beq_eq_true) tr3K,
    treeOK_of_eqWL (fun _ _ => Nat.eq_of_beq_eq_true) tr4K,
    treeOK_of_eqWL (fun _ _ => Nat.eq_of_beq_eq_true) tr5K,
    treeOK_of_eqWL (fun _ _ => Nat.eq_of_beq_eq_true) tr6K,
    treeOK_of_eqWL (fun _ _ => Nat.eq_of_beq_eq_true) tr7K,
    treeOK_of_eqWL (fun _ _ => Nat.eq_of_beq_eq_true) trFBK, treeOK_of_eqWL eqWL_nat trFLLK]
  rfl

theorem tg0K : eqWL (eqWL (eqWL (eqWL Nat.beq))) TGT0 (chunks TG0.length (chunks TG0.length TG0)) =
    true := by quickRfl
theorem tg1K : eqWL (eqWL (eqWL (eqWL Nat.beq))) TGT1 (chunks TG1.length (chunks TG1.length TG1)) =
    true := by quickRfl
theorem tg2K : eqWL (eqWL (eqWL (eqWL Nat.beq))) TGT2 (chunks TG2.length (chunks TG2.length TG2)) =
    true := by quickRfl
theorem tg3K : eqWL (eqWL (eqWL (eqWL Nat.beq))) TGT3 (chunks TG3.length (chunks TG3.length TG3)) =
    true := by quickRfl
theorem tg4K : eqWL (eqWL (eqWL (eqWL Nat.beq))) TGT4 (chunks TG4.length (chunks TG4.length TG4)) =
    true := by quickRfl
theorem tg5K : eqWL (eqWL (eqWL (eqWL Nat.beq))) TGT5 (chunks TG5.length (chunks TG5.length TG5)) =
    true := by quickRfl
theorem tg6K : eqWL (eqWL (eqWL (eqWL Nat.beq))) TGT6 (chunks TG6.length (chunks TG6.length TG6)) =
    true := by quickRfl

theorem tg_tr0 : treeOK TGT0 TG0 = true := treeOK_of_eqWL eqWL_nat tg0K
theorem tg_tr1 : treeOK TGT1 TG1 = true := treeOK_of_eqWL eqWL_nat tg1K
theorem tg_tr2 : treeOK TGT2 TG2 = true := treeOK_of_eqWL eqWL_nat tg2K
theorem tg_tr3 : treeOK TGT3 TG3 = true := treeOK_of_eqWL eqWL_nat tg3K
theorem tg_tr4 : treeOK TGT4 TG4 = true := treeOK_of_eqWL eqWL_nat tg4K
theorem tg_tr5 : treeOK TGT5 TG5 = true := treeOK_of_eqWL eqWL_nat tg5K
theorem tg_tr6 : treeOK TGT6 TG6 = true := treeOK_of_eqWL eqWL_nat tg6K

end CertificateChecks.KernelJ4Fam
