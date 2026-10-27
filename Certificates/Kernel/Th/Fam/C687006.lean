module

public import Certificates.Kernel.Th.JLet.Chk
public import Certificates.Kernel.Th.Fam.C687006Data
public import CFSG.Sporadic.Th.Recog.PlacementInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTh.Fam.C6

open CFSG.KC.Th CFSG.KC.Th.SurjS CFSG.KD.ThS CFSG.Sporadic.Th.Recog CFSG.Sporadic.Th.Recog.Place

@[expose] noncomputable def codeN {n : ℕ} (w : List (Fin n × Bool)) : List Nat :=
  w.map fun l => Nat.add (Nat.mul 2 l.1.val) (Bool.rec (motive := fun _ => Nat) 1 0 l.2)

@[expose] noncomputable def wP {n : ℕ} (R : Nat → Nat) (w : List (Fin n × Bool)) : Nat :=
  wordV R c rm (codeN w) ONE

@[expose] noncomputable def mP (A B : Nat) : Nat := mulB c rm A B

@[expose] noncomputable def regOf (f fi : Nat → Nat) (r : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (fi (Nat.sub r 9)) (f (Nat.sub r 1)) (Nat.blt r 9)

@[expose] noncomputable def pinsB (F G : Nat → Nat) (rs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => Bool.rec (motive := fun _ => Bool) false ih (Nat.beq (F r) (G r))) rs

@[expose] noncomputable def forceB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def notInB (x : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun y _ ih => Bool.rec (motive := fun _ => Bool) ih false (Nat.beq x y)) l

@[expose] noncomputable def nodupB (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x t ih => Bool.rec (motive := fun _ => Bool) false ih (notInB x t)) l

@[expose] def hWordN (j : Nat) : List (Fin 6 × Bool) := hWord (Fin.ofNat 5 j)

@[expose] noncomputable def lvL : Nat → Nat :=
  regOf (fun j => wP CFSG.KD.Th687006.RH (JLet.lWordN j))
    (fun j => wP CFSG.KD.Th687006.RH (FreeGroup.invRev (JLet.lWordN j)))

@[expose] noncomputable def lvC : Nat → Nat :=
  regOf (fun j => wP CFSG.KD.Th687006.RL (hWordN j))
    (fun j => wP CFSG.KD.Th687006.RL (FreeGroup.invRev (hWordN j)))

theorem k687006_pinH0 : pinsB CFSG.KD.Th687006.RH JLet.RH [1, 2, 3, 4] = true := by quickRfl
theorem k687006_pinH1 : pinsB CFSG.KD.Th687006.RH JLet.RH [5, 6, 7, 8] = true := by quickRfl
theorem k687006_pinH2 : pinsB CFSG.KD.Th687006.RH JLet.RH [9, 10, 11, 12] = true := by quickRfl
theorem k687006_pinH3 : pinsB CFSG.KD.Th687006.RH JLet.RH [13, 14, 15, 16] = true := by quickRfl
theorem k687006_pinL0 : pinsB CFSG.KD.Th687006.RL lvL [1, 2, 3, 9, 10, 11] = true := by quickRfl
theorem k687006_pinL1 : pinsB CFSG.KD.Th687006.RL lvL [4, 5, 6, 12, 13, 14] = true := by quickRfl
theorem k687006_pinC :
    pinsB CFSG.KD.Th687006.RC lvC [1, 2, 3, 4, 5, 9, 10, 11, 12, 13] = true := by quickRfl

@[expose] noncomputable def aP : Nat := CFSG.KD.Th687006.RH 1

@[expose] noncomputable def dP : Nat := CFSG.KD.Th687006.RH 4

@[expose] noncomputable def dIP : Nat := CFSG.KD.Th687006.RH 12

@[expose] noncomputable def vP (i : Fin 2) : Nat := wP CFSG.KD.Th687006.RH (vWord i)

@[expose] noncomputable def vIP (i : Fin 2) : Nat :=
  wP CFSG.KD.Th687006.RH (FreeGroup.invRev (vWord i))

@[expose] noncomputable def wpP (i : Fin 2) : Nat := wP CFSG.KD.Th687006.RL (wpWord i)

@[expose] noncomputable def wpIP (i : Fin 2) : Nat :=
  wP CFSG.KD.Th687006.RL (FreeGroup.invRev (wpWord i))

@[expose] noncomputable def repP (i : Fin 2) (m : Fin 8) : Nat :=
  wP CFSG.KD.Th687006.RC (repWord i m)

@[expose] noncomputable def zP (i : Fin 2) (m : Fin 8) : Nat := mP (wpP i) (repP i m)

@[expose] noncomputable def zIP (i : Fin 2) (m : Fin 8) : Nat :=
  mP (wP CFSG.KD.Th687006.RC (FreeGroup.invRev (repWord i m))) (wpIP i)

@[expose] noncomputable def orbP (i : Fin 2) (r : Fin 18) : Nat :=
  mP (mP (wP CFSG.KD.Th687006.RC (orbWord i r)) (vP i))
    (wP CFSG.KD.Th687006.RC (FreeGroup.invRev (orbWord i r)))

@[expose] noncomputable def fourP (i : Fin 2) (u : Fin 4) : Nat :=
  match u with
  | 0 => ONE
  | 1 => aP
  | 2 => vP i
  | 3 => mP aP (vP i)

@[expose] noncomputable def cntP (i : Fin 2) (q : Fin 32) : Nat :=
  mP (repP i (split32 q).1) (fourP i (split32 q).2)

@[expose] noncomputable def ord8P (X : Nat) : Bool :=
  forceB (mP X X) fun X2 => forceB (mP X2 X2) fun X4 =>
    Nat.beq (mP X4 X4) ONE && !Nat.beq X4 ONE

@[expose] noncomputable def cubeNeP (X : Nat) : Bool := !Nat.beq (mP (mP X X) X) ONE

@[expose] noncomputable def gensP (x : Fin 2) (j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (zP 1 (pair x).2) (zP 0 (pair x).1) (Nat.beq j 2))
    (Bool.rec (motive := fun _ => Nat) (vP 1) (vP 0) (Nat.beq j 0)) (Nat.blt j 2)

@[expose] noncomputable def gensIP (x : Fin 2) (j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (zIP 1 (pair x).2) (zIP 0 (pair x).1) (Nat.beq j 2))
    (Bool.rec (motive := fun _ => Nat) (vIP 1) (vIP 0) (Nat.beq j 0)) (Nat.blt j 2)

@[expose] noncomputable def chkA : Bool :=
  Nat.beq (wP CFSG.KD.Th687006.RC aHWord) aP && Nat.beq (mP aP aP) ONE

@[expose] noncomputable def chkV : Bool :=
  (List.finRange 2).all (fun i =>
    Nat.beq (mP (vP i) (vP i)) ONE && Nat.beq (mP aP (vP i)) (mP (vP i) aP)) &&
    Nat.beq (mP (mP (vP 0) (vP 1)) (mP (vP 0) (vP 1))) aP

@[expose] noncomputable def chkH : Bool :=
  (List.finRange 5).all fun j =>
    Nat.beq (mP (CFSG.KD.Th687006.RC (j.val + 1)) aP) (mP aP (CFSG.KD.Th687006.RC (j.val + 1)))

@[expose] noncomputable def chkOrb : Bool :=
  (List.finRange 2).all fun i => nodupB (List.ofFn fun r => orbP i r)

@[expose] noncomputable def chkRep : Bool :=
  (List.finRange 2).all fun i => (List.finRange 8).all fun m =>
    Nat.beq (mP (repP i m) (vP i)) (mP (vP i) (repP i m))

@[expose] noncomputable def chkCent : Bool :=
  (List.finRange 2).all fun i => nodupB (List.ofFn fun q => cntP i q)

@[expose] noncomputable def chkWp : Bool :=
  (List.finRange 2).all fun i =>
    Nat.beq (mP (mP (wpP i) aP) (wpIP i)) (vP i) &&
      Nat.beq (mP (mP (wpP i) (vP i)) (wpIP i)) (mP aP (vP i))

@[expose] noncomputable def chkCoset : Bool :=
  (List.finRange 2).all fun i => (List.finRange 8).all fun m =>
    (good i).contains m ||
      (List.finRange 4).all (fun u => cubeNeP (mP (zP i m) (fourP i u))) ||
      ord8P (mP (vP (1 - i)) (zP i m))

@[expose] noncomputable def chkPair : Bool :=
  (good 0).all fun m₀ => (good 1).all fun m₁ =>
    pair 0 == (m₀, m₁) || pair 1 == (m₀, m₁) ||
      ord8P (mP (zP 0 m₀) (mP (mP dP (mP (vP 0) (zP 1 m₁))) dIP))

@[expose] noncomputable def chkXw : Bool :=
  (List.finRange 2).all fun x =>
    [Twist.id, .f1, .f3, .f13].all fun k => (List.finRange 2).all fun j =>
      Nat.beq (wP CFSG.KD.Th687006.RH (xw (k, x) j))
        (wP (regOf (gensP x) (gensIP x)) (xwExpr k x j))

theorem k687006_A : chkA = true := by quickRfl
theorem k687006_V : chkV = true := by quickRfl
theorem k687006_H : chkH = true := by quickRfl
theorem k687006_Orb : chkOrb = true := by quickRfl
theorem k687006_Rep : chkRep = true := by quickRfl
theorem k687006_Cent : chkCent = true := by quickRfl
theorem k687006_Wp : chkWp = true := by quickRfl
theorem k687006_Coset : chkCoset = true := by quickRfl
theorem k687006_Pair : chkPair = true := by quickRfl
theorem k687006_Xw : chkXw = true := by quickRfl

end CertificateChecks.KernelTh.Fam.C6

namespace CertificateChecks.KernelTh.Fam

open C6

@[expose] noncomputable def check6K : Bool :=
  chkA && chkV && chkH && chkOrb && chkRep && chkCent && chkWp && chkCoset && chkPair && chkXw

theorem ok687006 : check6K = true := by
  rw [check6K, k687006_A, k687006_V, k687006_H, k687006_Orb, k687006_Rep, k687006_Cent,
    k687006_Wp, k687006_Coset, k687006_Pair, k687006_Xw]
  rfl

end CertificateChecks.KernelTh.Fam

end
