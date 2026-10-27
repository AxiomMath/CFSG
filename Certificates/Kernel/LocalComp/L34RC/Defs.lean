module

public import Certificates.Kernel.LocalComp.L34RC.Data
public import Certificates.Kernel.LocalComp.L34SChk
public import Certificates.Data.Kernel.L34Pow
public import Certificates.Data.Kernel.L34Scan

public section

namespace CertificateChecks.KernelLC.L34RC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Scan
open CFSG.KC.L34Scan2 CFSG.KC.L34Pow CertificateChecks.KernelLC.L34X
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def iterPt (x k p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) p (fun _ q => pg 6 (mask 6) x q) k

@[expose] noncomputable def retK (x p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => 0)
    (fun _ ih q k => Bool.rec (ih (pg 6 (mask 6) x q) (Nat.succ k)) k (Nat.beq q p))
    (nat_lit 42) (pg 6 (mask 6) x p) (nat_lit 1)

@[expose] noncomputable def sqPt (f x : Nat) : Bool :=
  orB (andB (Nat.blt 0 f) (andB (Nat.ble f 20160)
      (Nat.beq (L34S.T (Nat.sub f 1)) (pcomp 42 6 (mask 6) x x))))
    (notB (allN 42 fun p => strictB (retK x p) fun L =>
      notB (andB (Nat.beq (iterPt x L p) p) (notB (Nat.beq (iterPt x (Nat.mod 256 L) p) p)))))

@[expose] noncomputable def cenPt (r m : Nat) (C : Nat → Nat) (e x : Nat) : Bool :=
  orB (notB (commPt 42 6 x r)) (orB (notB (allN m fun c => commPt 42 6 x (C c)))
    (orB (Nat.beq x e) (Nat.beq x r)))

@[expose] noncomputable def oddPt (r : Nat) (C : Nat → Nat) (e x : Nat) : Bool :=
  orB (notB (commPt 42 6 x r)) (orB (Nat.beq x e) (orB (notB (with945 x fun y => Nat.beq y e))
    (Nat.ble (CFSG.KC.HeAutK.cntR (fun c => commPt 42 6 x (C c)) 0 64) 4)))

@[expose] noncomputable def invPt4 (nU r e x : Nat) : Bool :=
  orB (notB (commPt 42 6 x r)) (orB (notB (invPt 42 6 x)) (orB (Nat.beq x e) (memL nU L34RU.U x)))

@[expose] noncomputable def allPt (r1 r2 r3 r4 e f x : Nat) : Bool :=
  andB (sqPt f x) (andB (cenPt r2 168 L34C2.P e x) (andB (cenPt r3 60 L34C3.P e x)
    (andB (oddPt r1 L34C1.P e x) (invPt4 91 r4 e x))))

@[expose] noncomputable def rc22207 (lo n : Nat) : Bool :=
  strictB (pidn 42 6) fun e => strictB (RP 0) fun r1 => strictB (RP 1) fun r2 =>
    strictB (RP 2) fun r3 => strictB (RP 3) fun r4 =>
      allN n fun s => allN 1344 fun t =>
        strictB (Nat.add (Nat.mul 1344 (Nat.add lo s)) t) fun i =>
          strictB (L34R.T i) fun x => allPt r1 r2 r3 r4 e (L34RU.Q i) x

@[expose] noncomputable def topK (e s n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
    (fun _ ih s => strictN (pcomp 42 6 (mask 6) s s) fun s2 =>
      Bool.rec (motive := fun _ => Nat) (ih s2) s (Nat.beq s2 e)) n s

@[expose] noncomputable def fourPair (r e u v : Nat) : Bool :=
  orB (commPt 42 6 u v) (strictB (pcomp 42 6 (mask 6) u v) fun s =>
    orB (notB (Nat.beq (pow2K 42 6 8 s) e)) (strictB (topK e s 8) fun z =>
      andB (Nat.beq (pcomp 42 6 (mask 6) z z) e) (andB (notB (Nat.beq z e))
        (andB (commPt 42 6 z u) (andB (notB (Nat.beq z r))
          (andB (notB (Nat.beq z (pcomp 42 6 (mask 6) r u))) (notB (Nat.beq z u))))))))

@[expose] noncomputable def fourRows (lo n : Nat) : Bool :=
  strictB (pidn 42 6) fun e => strictB (RP 3) fun r =>
    allN n fun a => strictB (L34RU.U (Nat.add lo a)) fun u =>
      allN 91 fun b => fourPair r e u (L34RU.U b)

end CertificateChecks.KernelLC.L34RC

end
