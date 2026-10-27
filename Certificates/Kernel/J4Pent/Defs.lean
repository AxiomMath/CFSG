module

public import Certificates.Data.Kernel.J4Pent
public import Certificates.Kernel.J4Pent.Data
public import Certificates.Kernel.J4Q.QTData
public import Certificates.Kernel.J4Q.X0OrbMats
public import Certificates.Data.CFSGNative.J4.Data

public section

namespace CertificateChecks.KernelJ4Pent

open CFSG.KC.J4Pent CFSG.KD.J4Pent CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.Loop

@[expose] noncomputable def ONES : Nat := Nat.sub (Nat.shiftLeft 1 NL) 1

@[expose] noncomputable def TSR : List Nat := tabsW NL R 28

@[expose] noncomputable def RT : List Nat := dropK 96 R

@[expose] noncomputable def tiesAt (t : Nat) : List Nat × List Nat :=
  nthL ([], []) (nthL [] TB (Nat.div t 64)) (Nat.mod t 64)

@[expose] noncomputable def canonF (t : Nat) : Bool :=
  bIf(Nat.beq t 0, true,
    canonAt NL ONES 16 TSR RT (trJ t0 t1 t2 t3 t4 t5 t6 (CFSG.KD.X0O.MSF t))
      (Nat.lor (maskOf (tiesAt t).1) (maskOf (tiesAt t).2)))

@[expose] noncomputable def tieF (t : Nat) : Bool :=
  (fun M => bAnd(allB (fun l => Nat.beq (vecJ rm (laneV R l) M) (laneV R l)) (tiesAt t).1,
      allB (fun l => Nat.blt (laneV R l) (vecJ rm (laneV R l) M)) (tiesAt t).2))
  (CFSG.KD.X0O.MSF t)

@[expose] noncomputable def startK (k : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) R
    (fun _ Y => appT (trJ t0 t1 t2 t3 t4 t5 t6 (getN one XG 0)) (tabsT Y 28) 0 112) k

@[expose] noncomputable def targetK (k : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (bcast ONES (v2N CFSG.Sporadic.J4.Native.rootV))
    (fun j _ => nthL [] Z j) k

@[expose] noncomputable def walkF (k : Nat) : Bool :=
  eqL (walkT ONES (trJ t0 t1 t2 t3 t4 t5 t6 Ai) (trJ t0 t1 t2 t3 t4 t5 t6 Bi)
    (trJ t0 t1 t2 t3 t4 t5 t6 B) WS (startK k)) (targetK k)

@[expose] noncomputable def UT : List Nat :=
  mapS (trJ t0 t1 t2 t3 t4 t5 t6) [U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10]

@[expose] noncomputable def Z4 : List Nat :=
  zipS Nat.lor (zipS Nat.lor (nthL [] Z 0) (mapS (fun x => Nat.shiftLeft x NL) (nthL [] Z 1)))
    (zipS Nat.lor (mapS (fun x => Nat.shiftLeft x (Nat.mul 2 NL)) (nthL [] Z 2))
      (mapS (fun x => Nat.shiftLeft x (Nat.mul 3 NL)) (nthL [] Z 3)))

@[expose] noncomputable def eFlags : Nat :=
  pairFlags NL ONES (Nat.sub (Nat.shiftLeft 1 (Nat.mul 4 NL)) 1) 8
    (subsT UT 0 5 Z4) (subsT UT 5 6 Z4)

@[expose] noncomputable def stepWf (s : Nat × Nat × Nat) : Bool :=
  bAnd(Nat.blt (Nat.lor s.1 (Nat.lor s.2.1 s.2.2)) (Nat.shiftLeft 1 NL),
    bAnd(Nat.beq (Nat.land s.1 s.2.1) 0,
      bAnd(Nat.beq (Nat.land s.1 s.2.2) 0, Nat.beq (Nat.land s.2.1 s.2.2) 0)))

@[expose] noncomputable def pairLt (p q : Nat × Nat) : Bool :=
  bIf(Nat.blt p.1 q.1, true, bAnd(Nat.beq p.1 q.1, Nat.blt p.2 q.2))

@[expose] noncomputable def incrP (L : List (Nat × Nat)) : Option (Nat × Nat) → Bool :=
  List.rec (motive := fun _ => Option (Nat × Nat) → Bool) (fun _ => true)
    (fun p _ ih prev => Option.rec (motive := fun _ => Bool) (ih (some p))
      (fun q => bAnd(pairLt q p, ih (some p))) prev) L

@[expose] noncomputable def mapP (L : List Nat) : List (Nat × Nat) :=
  List.rec (motive := fun _ => List (Nat × Nat)) List.nil (fun l _ ih => List.cons (0, l) ih) L

@[expose] noncomputable def memN (n : Nat) (L : List Nat) : Bool := anyB (fun x => Nat.beq x n) L

@[expose] noncomputable def fixTotal : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun blk _ ih => strictN ih fun r => Nat.add r
    (List.rec (motive := fun _ => Nat) 0 (fun p _ ih2 => strictN ih2 fun r2 => Nat.add r2 (lenK p.1))
      blk)) TB

@[expose] noncomputable def runSum (L : List (Nat × Nat)) : Nat → Nat → Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat × Nat)
    (fun _ f => Bool.rec (motive := fun _ => Nat × Nat) (Nat.div 6720 (Nat.succ f), 1) (0, 0)
      (Nat.beq f 0))
    (fun p _ ih l f => Bool.rec (motive := fun _ => Nat × Nat)
      ((fun r => Bool.rec (motive := fun _ => Nat × Nat)
          (Nat.add r.1 (Nat.div 6720 (Nat.succ f)), Nat.succ r.2) r (Nat.beq f 0))
        (ih p.1 1))
      (ih l (Nat.succ f))
      (bAnd(Nat.beq p.1 l, Nat.blt 0 f)))
    L

@[expose] noncomputable def witF (j : Nat) : Bool :=
  Nat.beq (vecJ rm (nthL 0 D4 j) (CFSG.KD.X0O.MSF (nthL (0, 0) WD j).2))
    (laneV R (nthL (0, 0) WD j).1)

end CertificateChecks.KernelJ4Pent

end
