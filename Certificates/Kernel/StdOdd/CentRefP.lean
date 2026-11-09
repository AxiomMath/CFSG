module

public import Certificates.Kernel.StdOdd.CentRefSeg
public import Certificates.Data.Kernel.StdOdd.ChainP

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain CFSG.KC.StdOdd.ChainP CFSG.KC.Misc.E6Std
  CFSG.KC.LQT.P

namespace CentData

variable (D : CentData)

@[expose] noncomputable def rchP (A B RK K ri : ℕ) (O : List ℕ) (Sr : List (List (List ℕ)))
    (l k : ℕ) : Bool :=
  forceLB (D.rkP RK K ri O (Nat.add (Nat.mul l K) k)) fun U =>
  andB (bdB U) (forceB c0P fun c0 =>
  walkP c0 (D.refLet A B l) (spreadS (sliceL (Nat.mul 20 k) 20 (Sr.getD l [])) 1 (lenN D.eL))
      (packP U) fun P => forceLB (unpackP P) fun T =>
    andB (Nat.beq (neqMask T (D.rkP RK K ri O (Nat.succ (Nat.add (Nat.mul l K) k)))) 0)
      (Bool.rec (motive := fun _ => Bool) true
        (Nat.beq (Nat.land (neqV T (nthN D.βs l) (Nat.succ l)) (Nat.shiftLeft 1 l)) 0)
        (Nat.beq (Nat.succ k) K)))

@[expose] noncomputable def segP (A B ck m k : ℕ) : Bool :=
  forceLB (D.ckP ck k) fun U =>
  andB (bdB U) (forceB c0P fun c0 =>
  walkP c0 [A, B] (stepsPl (Nat.shiftRight D.R0 (Nat.mul (Nat.mul 320
      (Nat.div (Nat.add (lenN D.reps) 7) 8)) k)) (Nat.div (Nat.add (lenN D.reps) 7) 8)
      (lenN D.reps) (Nat.min 20 (Nat.sub D.r0D (Nat.mul 20 k))) 2) (packP U) fun P =>
    forceLB (unpackP P) fun V =>
    Bool.rec (motive := fun _ => Bool) (Nat.beq (neqMask V (D.ckP ck (Nat.succ k))) 0)
      (Nat.beq (neqV V D.bv (lenN D.reps)) 0) (Nat.beq (Nat.succ k) m))

end CentData

@[expose] noncomputable def shiftS (S : List (List ℕ)) (off : ℕ) : List (List ℕ) :=
  List.rec (motive := fun _ => List (List ℕ)) List.nil
    (fun ms _ ih => List.cons (List.rec (motive := fun _ => List ℕ) List.nil
      (fun m _ ih' => List.cons (Nat.shiftRight m off) ih') ms) ih) S

@[expose] noncomputable def stepsB (Ms : List ℕ) (S : List (List ℕ)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun ms _ ih => andB (andB (Nat.beq (lenN ms) (lenN Ms)) (disjL ms)) ih) S

@[expose] noncomputable def blkP (Ms : List ℕ) (S : List (List ℕ)) (U : List ℕ) (n β b : ℕ) :
    Bool :=
  forceLB (chunkPl U (Nat.mul 156 b) 156) fun W =>
  andB (bdB W) (forceB c0P fun c0 =>
  walkP c0 Ms (shiftS S (Nat.mul 156 b)) (packP W) fun P => forceLB (unpackP P) fun V =>
    Nat.beq (neqV V β (Nat.min 156 (Nat.sub n (Nat.mul 156 b)))) 0)

@[expose] noncomputable def walkBP (Ms : List ℕ) (S : List (List ℕ)) (U : List ℕ) (n β : ℕ) :
    Bool :=
  forceLB Ms fun Ms => andB (stepsB Ms S) (Nat.rec (motive := fun _ => Bool) true
    (fun b ih => andB (blkP Ms S U n β b) ih) (Nat.div (Nat.add n 155) 156))

@[expose] noncomputable def forestP (FPn WN bw n D : ℕ) (Ms : List ℕ) (β : ℕ) : Bool :=
  forceLB (splitPl FPn bw n 156) fun F => andB (sortOK F n)
    (walkBP Ms (stepsPl WN bw n D (lenN Ms)) F n β)

namespace CentData

variable (D : CentData)

@[expose] noncomputable def levP (j : ℕ) : Bool :=
  andB (allL (D.RI j) fun r => andB (Nat.blt r (lenN D.V)) (fixesOK (nthV D.V r) D.βs j))
    (forestP (D.FP j) (D.WN j) (Nat.div (Nat.add (D.nf j) 7) 8) (D.nf j) (D.Df j)
      ((D.RI j).map (nthV D.V)) (nthN D.βs j))

@[expose] noncomputable def levQ (t j : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) (D.levOK j) (D.levP j) (Nat.ble (D.nf j) t)

@[expose] noncomputable def startP (A B : ℕ) : Bool :=
  walkBP [A, B] (stepsPl D.R0 (Nat.div (Nat.add (lenN D.reps) 7) 8) (lenN D.reps) D.r0D 2)
    (vecsPl D.reps) (lenN D.reps) D.bv

end CentData

end CFSG.KD.StdOdd.Cent

end
