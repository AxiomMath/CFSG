module

public import Certificates.Kernel.Th.DModel.Mat
public import Certificates.Kernel.Th.Fam.K
public import Certificates.Kernel.Th.JLet.Mats
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTh.JLet

open CFSG.KC.Th CFSG.KC.Th.SurjS CFSG.KD.ThS CFSG.Sporadic.Th.Recog
open CertificateChecks.KernelTh.DModel (codeW)
open CertificateChecks.KernelTh.Fam (thK)
open CFSG.KC.Th.Expr (TE)
open CFSG.GH74.QTGen4.Recog.G23 (g23Words)

@[expose] noncomputable def cC : List Nat := codeW cWord

@[expose] noncomputable def cI : List Nat := codeW (FreeGroup.invRev cWord)

@[expose] noncomputable def hV (x : Nat) : Nat :=
  wordV CFSG.KD.ThSj.RB c rm (List.append cC (x :: cI)) ONE

@[expose] noncomputable def regCode (r : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.add (Nat.mul 2 (Nat.sub r 9)) 1)
    (Nat.mul 2 (Nat.sub r 1)) (Nat.blt r 9)

@[expose] noncomputable def RH (r : Nat) : Nat := hV (regCode r)

@[expose] noncomputable def code6 (w : List (Fin 6 × Bool)) : List Nat :=
  w.map fun l => Nat.add (Nat.mul 2 l.1.val) (Bool.rec (motive := fun _ => Nat) 1 0 l.2)

@[expose] def lWordN (j : Nat) : List (Fin 8 × Bool) := lWord (Fin.ofNat 6 j)

@[expose] noncomputable def lV (j : Nat) : Nat := wordV RH c rm (codeW (lWordN j)) ONE

@[expose] noncomputable def lIV (j : Nat) : Nat :=
  wordV RH c rm (codeW (FreeGroup.invRev (lWordN j))) ONE

@[expose] noncomputable def RL (r : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (lIV (Nat.sub r 9)) (lV (Nat.sub r 1)) (Nat.blt r 9)

@[expose] noncomputable def lVRB (j : Nat) : Nat :=
  wordV CFSG.KD.ThSj.RB c rm (codeW (lWordN j)) ONE

@[expose] noncomputable def lIVRB (j : Nat) : Nat :=
  wordV CFSG.KD.ThSj.RB c rm (codeW (FreeGroup.invRev (lWordN j))) ONE

@[expose] noncomputable def RLRB (r : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (lIVRB (Nat.sub r 9)) (lVRB (Nat.sub r 1)) (Nat.blt r 9)

@[expose] noncomputable def RLJ (r : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    ([lIMatJ0, lIMatJ1, lIMatJ2, lIMatJ3, lIMatJ4, lIMatJ5].getD (Nat.sub r 9) 0)
    ([lMatJ0, lMatJ1, lMatJ2, lMatJ3, lMatJ4, lMatJ5].getD (Nat.sub r 1) 0) (Nat.blt r 9)

@[expose] noncomputable def wjV (k : Fin 8) : Nat :=
  TE.pk thK (.mul (.word (wJ k)) (.pow .a (εJ k)))

@[expose] noncomputable def aV : Nat := TE.pk thK .a

@[expose] noncomputable def relsV (R : Nat → Nat) (ws : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => Bool.rec (motive := fun _ => Bool) false ih (Nat.beq (wordV R c rm w ONE) ONE))
    ws

@[expose] noncomputable def commV (A B : Nat) : Bool := Nat.beq (mulB c rm A B) (mulB c rm B A)

theorem k687002_a : Nat.beq (hV 0) aV = true := by quickRfl

theorem k687002_b : BigS.notB (Nat.beq (hV 2) aV) = true := by quickRfl

theorem k687002_ci :
    Nat.beq (wordV CFSG.KD.ThSj.RB c rm (List.append cC cI) ONE) ONE = true := by quickRfl

theorem k687002_ic :
    Nat.beq (wordV CFSG.KD.ThSj.RB c rm (List.append cI cC) ONE) ONE = true := by quickRfl

theorem k687002_c0 : commV (CFSG.KD.ThSj.RB 1) (CFSG.KD.ThSj.RB 1) = true := by quickRfl
theorem k687002_c2 : commV (CFSG.KD.ThSj.RB 1) (CFSG.KD.ThSj.RB 3) = true := by quickRfl
theorem k687002_c3 : commV (CFSG.KD.ThSj.RB 1) (CFSG.KD.ThSj.RB 4) = true := by quickRfl
theorem k687002_c4 : commV (CFSG.KD.ThSj.RB 1) (CFSG.KD.ThSj.RB 5) = true := by quickRfl
theorem k687002_c5 : commV (CFSG.KD.ThSj.RB 1) (CFSG.KD.ThSj.RB 6) = true := by quickRfl
theorem k687002_c6 : commV (CFSG.KD.ThSj.RB 1) (CFSG.KD.ThSj.RB 7) = true := by quickRfl
theorem k687002_c7 : commV (CFSG.KD.ThSj.RB 1) (CFSG.KD.ThSj.RB 8) = true := by quickRfl

theorem k687002_m0 : Nat.beq (lVRB 0) lMatJ0 = true := by quickRfl
theorem k687002_m1 : Nat.beq (lVRB 1) lMatJ1 = true := by quickRfl
theorem k687002_m2 : Nat.beq (lVRB 2) lMatJ2 = true := by quickRfl
theorem k687002_m3 : Nat.beq (lVRB 3) lMatJ3 = true := by quickRfl
theorem k687002_m4 : Nat.beq (lVRB 4) lMatJ4 = true := by quickRfl
theorem k687002_m5 : Nat.beq (lVRB 5) lMatJ5 = true := by quickRfl

theorem k687002_mi0 : Nat.beq (lIVRB 0) lIMatJ0 = true := by quickRfl
theorem k687002_mi1 : Nat.beq (lIVRB 1) lIMatJ1 = true := by quickRfl
theorem k687002_mi2 : Nat.beq (lIVRB 2) lIMatJ2 = true := by quickRfl
theorem k687002_mi3 : Nat.beq (lIVRB 3) lIMatJ3 = true := by quickRfl
theorem k687002_mi4 : Nat.beq (lIVRB 4) lIMatJ4 = true := by quickRfl
theorem k687002_mi5 : Nat.beq (lIVRB 5) lIMatJ5 = true := by quickRfl

theorem k687002_rels : relsV RLJ (g23Words.map code6) = true := by quickRfl

theorem k687002_t0 : commV (lVRB 0) (CFSG.KD.ThSj.RB 7) = true := by quickRfl
theorem k687002_t1 : commV (lVRB 1) (CFSG.KD.ThSj.RB 7) = true := by quickRfl
theorem k687002_t2 : commV (lVRB 2) (CFSG.KD.ThSj.RB 7) = true := by quickRfl
theorem k687002_t3 : commV (lVRB 3) (CFSG.KD.ThSj.RB 7) = true := by quickRfl
theorem k687002_t4 : commV (lVRB 4) (CFSG.KD.ThSj.RB 7) = true := by quickRfl
theorem k687002_t5 : commV (lVRB 5) (CFSG.KD.ThSj.RB 7) = true := by quickRfl

theorem k687002_l0 : BigS.notB (Nat.beq (lVRB 0) ONE) = true := by quickRfl

theorem k687002_w2 : Nat.beq (hV 4) (wjV 2) = true := by quickRfl
theorem k687002_w3 : Nat.beq (hV 6) (wjV 3) = true := by quickRfl
theorem k687002_w4 : Nat.beq (hV 8) (wjV 4) = true := by quickRfl
theorem k687002_w5 : Nat.beq (hV 10) (wjV 5) = true := by quickRfl
theorem k687002_w6 : Nat.beq (hV 12) (wjV 6) = true := by quickRfl
theorem k687002_w7 : Nat.beq (hV 14) (wjV 7) = true := by quickRfl

end CertificateChecks.KernelTh.JLet

end
