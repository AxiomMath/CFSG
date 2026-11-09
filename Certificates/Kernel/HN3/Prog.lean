module

public import Certificates.Kernel.HN3.Data
public import Certificates.Kernel.HN3.Ck
public import CFSG.Certificates.Kernel.HN3Sound
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HN3

section Split

open CFSG.KC.HN3 CFSG.KC.Ord CFSG.KC.HNF26720 CFSG.KC.HNF26729

@[expose] noncomputable def eqC (C : List Nat) (R : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun R => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) R)
    (fun c _ ih R => List.rec (motive := fun _ => Bool) false
      (fun r t _ => andB (Nat.beq c r) (ih t)) R) C R

theorem andB_tt {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b
  · exact absurd h Bool.false_ne_true
  · exact absurd h Bool.false_ne_true
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, rfl⟩

theorem eqC_eq : ∀ (C R : List Nat), eqC C R = true → R = C
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | c :: C, r :: R, h => by
    obtain ⟨h1, h2⟩ := andB_tt (a := Nat.beq c r) (b := eqC C R) h
    rw [Nat.eq_of_beq_eq_true h1, eqC_eq C R h2]

@[expose] noncomputable def finK (regs : List Nat) (R : List Nat) : Bool :=
  andB (Nat.beq (getN 0 R 22) (getN 0 regs 0)) (andB (Nat.beq (getN 0 R 23) (getN 0 regs 1))
  (andB (Nat.beq (getN 0 R 24) (getN 0 regs 2)) (andB (Nat.beq (getN 0 R 25) (getN 0 regs 3))
  (andB (Nat.beq (getN 0 R 26) (getN 0 regs 4)) (Nat.beq (getN 0 R 27) (getN 0 regs 5))))))

@[expose] noncomputable def runL (mul : Nat → Nat → Nat) : List (List Nat) → List Nat → List Nat
  | [], R => R
  | c :: P, R => runL mul P (stepM mul R c)

theorem runM_eq (mul : Nat → Nat → Nat) :
    ∀ (P : List (List Nat)) (R : List Nat) (k : List Nat → Bool), runM mul P R k = k (runL mul P R)
  | [], _, _ => rfl
  | c :: P, R, k => by
    change forceLB (stepM mul R c) (fun R' => runM mul P R' k) = _
    rw [CFSG.KS.HN3.forceLB_eq]
    exact runM_eq mul P _ k

theorem runM_append (mul : Nat → Nat → Nat) :
    ∀ (P Q : List (List Nat)) (R : List Nat) (k : List Nat → Bool),
      runM mul (P ++ Q) R k = runM mul P R (fun R' => runM mul Q R' k)
  | [], _, _, _ => rfl
  | c :: P, Q, R, k => by
    change forceLB (stepM mul R c) (fun R' => runM mul (P ++ Q) R' k) =
      forceLB (stepM mul R c) (fun R' => runM mul P R' (fun R'' => runM mul Q R'' k))
    exact congrArg _ (funext fun R' => runM_append mul P Q R' k)

theorem runM_mono {mul : Nat → Nat → Nat} {P : List (List Nat)} {R C : List Nat}
    (h : runM mul P R (eqC C) = true) (k : List Nat → Bool) : runM mul P R k = k C := by
  rw [runM_eq] at h ⊢
  rw [eqC_eq C _ h]

theorem runM_ck {mul : Nat → Nat → Nat} {P : List (List Nat)} {R C : List Nat}
    {k : List Nat → Bool} (n : Nat) (h1 : runM mul (P.take n) R (eqC C) = true)
    (h2 : runM mul (P.drop n) C k = true) : runM mul P R k = true := by
  rw [← List.take_append_drop n P, runM_append, runM_mono h1]
  exact h2

theorem progK_of (mul : Nat → Nat → Nat) (A B ONE : Nat) (P : List (List Nat)) (regs : List Nat)
    (hA : Nat.beq (mul A A) ONE = true) (hB : Nat.beq (mul B (mul B B)) ONE = true)
    (h : runM mul P (initM ONE A B (mul B B)) (finK regs) = true) :
    progK mul A B ONE P regs = true := by
  have e : progK mul A B ONE P regs = andB (Nat.beq (mul A A) ONE)
      (andB (Nat.beq (mul B (mul B B)) ONE) (runM mul P (initM ONE A B (mul B B)) (finK regs))) := by
    unfold progK
    rw [CFSG.KS.HNF26720.strictB_eq]
    rfl
  rw [e, hA, hB]
  exact h

end Split

open CFSG.KC.HN3 (runM initM)

theorem prog_ok0 : runM mul (prog.take 126) (initM CFSG.KD.FamHNSeed.ONE (CFSG.KD.FamHNSeed.RW 1)
    (CFSG.KD.FamHNSeed.RW 2) (mul (CFSG.KD.FamHNSeed.RW 2) (CFSG.KD.FamHNSeed.RW 2)))
    (eqC ck1) = true := by
  quickRfl

theorem prog_ok1 : runM mul ((prog.drop 126).take 126) ck1 (eqC ck2) = true := by
  quickRfl

theorem prog_ok2 : runM mul (((prog.drop 126).drop 126).take 126) ck2 (eqC ck3) = true := by
  quickRfl

theorem prog_ok3 : runM mul (((prog.drop 126).drop 126).drop 126) ck3 (finK regs) = true := by
  quickRfl

theorem prog_ok : CFSG.KC.HN3.progK mul (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2)
    CFSG.KD.FamHNSeed.ONE prog regs = true :=
  progK_of mul _ _ _ prog regs (by quickRfl) (by quickRfl)
    (runM_ck 126 prog_ok0 (runM_ck 126 prog_ok1 (runM_ck 126 prog_ok2 prog_ok3)))

end CFSG.KD.HN3

end
