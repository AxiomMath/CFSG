module

public import Certificates.Kernel.MonsterExist.ShortKey.Data
public import CFSG.Certificates.Kernel.Common.Loop
public import Certificates.Data.Kernel.KDense.Twins
public import Certificates.Data.CFSGNative.MonsterAxis.Basic
public import CFSG.Monster.B.Rep4371.Model

public section

namespace CertificateChecks.MonsterExist.ShortKey

open CFSG.KC CFSG.KC.Loop CFSG.KC.KDense CFSG.Monster CFSG.Monster.B

@[expose] noncomputable def maskW (w : Nat) : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1)

@[expose] noncomputable def onesL (W n : Nat) : Nat := Nat.div (maskW (Nat.mul W n)) (maskW W)

@[expose] noncomputable def laneW (W v k : Nat) : Nat := fld(v, Nat.mul W k, maskW W)

@[expose] noncomputable def absentL (W n v d : Nat) : Bool :=
  (fun o => (fun h => Nat.beq (Nat.land (Nat.sub (Nat.lor h (Nat.xor v (Nat.mul d o))) o) h) h)
    (Nat.shiftLeft o (Nat.sub W (nat_lit 1)))) (onesL W n)

@[expose] noncomputable def bkt (a : Nat) : Nat := fld(SKO, Nat.mul (nat_lit 26) a, nat_lit 67108863)

@[expose] noncomputable def offB (e : Nat) : Nat := Nat.land e (nat_lit 131071)

@[expose] noncomputable def cntB (e : Nat) : Nat := Nat.shiftRight e (nat_lit 17)

@[expose] noncomputable def slice (T off n : Nat) : Nat :=
  fld(T, Nat.mul (nat_lit 13) off, maskW (Nat.mul (nat_lit 13) n))

@[expose] noncomputable def memK (x : Nat) : Bool :=
  (fun e => bIf(absentL (nat_lit 13) (cntB e) (slice SKV (offB e) (cntB e)) (Nat.shiftRight x (nat_lit 12)),
      false, true))
    (bkt (Nat.land x (nat_lit 4095)))

@[expose] noncomputable def cOf (a : Nat) : Nat := nIf(Nat.beq (Nat.land a (nat_lit 1)) (nat_lit 0), a, Nat.xor a (nat_lit 63))

@[expose] noncomputable def DU : Nat :=
  nat_lit 0xe607a09e001fd906d0b5002ffc8548a88037c0440480403b30210220203d0c104108103e

@[expose] noncomputable def pK (w : Nat) : Nat := Nat.land (Nat.shiftRight (popcT (nat_lit 24) w) (nat_lit 2)) (nat_lit 1)

@[expose] noncomputable def oddOK (a th wc pc d i : Nat) : Bool :=
  bAnd(Nat.blt i (nat_lit 24),
    bAnd(Nat.beq (Nat.xor (cOf a) (selB (Nat.xor (bitN wc i) pc) (nat_lit 63))) a,
      Nat.beq d (Nat.xor th (fld(DU, Nat.mul (nat_lit 12) i, nat_lit 4095)))))

@[expose] noncomputable def octOK (a th d δ a0 w : Nat) (ok8 : Bool) : Bool :=
  bAnd(ok8, bAnd(Nat.beq (Nat.land δ w) δ,
    (fun c => bAnd(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
      bAnd(Nat.beq (Nat.xor a0 (selB (Nat.land (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)) (nat_lit 63))) a,
        Nat.beq d (Nat.xor th (dualT δ))))) (popcT (nat_lit 24) δ)))

@[expose] noncomputable def pairOK (a d i j : Nat) : Bool :=
  bAnd(Nat.blt i j, bAnd(Nat.blt j (nat_lit 24),
    bAnd(bIf(Nat.beq a (nat_lit 0), true, Nat.beq a (nat_lit 63)),
      Nat.beq d (dualT (Nat.lor (Nat.shiftLeft (nat_lit 1) i) (Nat.shiftLeft (nat_lit 1) j))))))

structure Ctx where
  th : Nat
  wA : Nat
  wB : Nat
  okA : Bool
  okB : Bool

@[expose] noncomputable def entryOK (a : Nat) (C : Ctx) (d p : Nat) : Bool :=
  Ctx.rec (motive := fun _ => Bool) (fun th wA wB okA okB =>
    (fun t => bIf(Nat.beq t (nat_lit 0),
      (fun wc => oddOK a th wc (pK wc) d (Nat.land p (nat_lit 31)))
        (nIf(Nat.beq (Nat.land a (nat_lit 1)) (nat_lit 0), wA, wB)),
      bIf(Nat.beq t (nat_lit 1),
        (fun f => octOK a th d (Nat.land p (nat_lit 16777215)) (nIf(f, Nat.xor a (nat_lit 63), a))
            (nIf(f, wB, wA)) (bIf(f, okB, okA)))
          (Nat.beq (Nat.land (Nat.shiftRight p (nat_lit 24)) (nat_lit 1)) (nat_lit 1)),
        bIf(Nat.beq t (nat_lit 2),
          pairOK a d (Nat.land p (nat_lit 31)) (Nat.land (Nat.shiftRight p (nat_lit 5)) (nat_lit 31)),
          false))))
      (Nat.shiftRight p (nat_lit 28))) C

@[expose] noncomputable def laneOK (a : Nat) (C : Ctx) (vs ps k : Nat) : Bool :=
  (fun d => bAnd(Nat.blt d (nat_lit 4096), bAnd(entryOK a C d (laneW (nat_lit 32) ps k),
      bIf(Nat.beq k (nat_lit 0), true, Nat.blt (laneW (nat_lit 13) vs (Nat.sub k (nat_lit 1))) d))))
    (laneW (nat_lit 13) vs k)

@[expose] noncomputable def lanesOK (a : Nat) (C : Ctx) (vs ps n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => bAnd(laneOK a C vs ps k, ih)) n

@[expose] noncomputable def ctxOf (a : Nat) : Ctx :=
  (fun wA wB => ⟨thetaT a, wA, wB, Nat.beq (popcT (nat_lit 24) wA) (nat_lit 8),
    Nat.beq (popcT (nat_lit 24) wB) (nat_lit 8)⟩) (wordT a) (wordT (Nat.xor a (nat_lit 63)))

@[expose] noncomputable def bucketOK (a : Nat) : Bool :=
  (fun e => lanesOK a (ctxOf a) (slice SKV (offB e) (cntB e))
      (fld(SKP, Nat.mul (nat_lit 32) (offB e), maskW (Nat.mul (nat_lit 32) (cntB e)))) (cntB e))
    (bkt a)

@[expose] noncomputable def bucketsOK (lo n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => bAnd(bucketOK (Nat.add lo k), ih)) n

@[expose] noncomputable def countOK : Bool :=
  Nat.beq (sumBelow (nat_lit 4096) (nat_lit 64) (fun a => cntB (bkt a))) (nat_lit 98280)

end CertificateChecks.MonsterExist.ShortKey

end
