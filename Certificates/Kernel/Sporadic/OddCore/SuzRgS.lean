module

public import Certificates.Kernel.Sporadic.OddCore.SuzRgD
public import Certificates.Kernel.Sporadic.OddCore.SuzFbS
public import CFSG.Sporadic.SuzRecog.RigidL2Tests

public section

namespace CertificateChecks.KernelSpor.SuzRg

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.PEnum
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzMGF
  CertificateChecks.KernelSpor.SuzC1EG

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "pgk" => pg 11 (mask 11)
local notation "Id" => pidn 1782 11
local notation "g7" => pg 7 (mask 7)
local notation "W" => SuzFb.W
local notation "QE" => KernelLC.SuzB0QE

@[expose] noncomputable def fl (F k : Nat) : Nat := pg 11 (mask 11) F k

@[expose] noncomputable def inV (c j : Nat) : Bool := bAnd(Nat.beq c 0, Nat.blt j 4)

@[expose] noncomputable def ncAt (X Y p : Nat) : Bool :=
  bAnd(Nat.blt p 1782, Bool.not (Nat.beq (pgk X (pgk Y p)) (pgk Y (pgk X p))))

@[expose] noncomputable def ncvAt (X Y i z : Nat) : Bool :=
  bAnd(Nat.blt z 1782, Bool.not (Nat.beq (pgk X (pgk Y z)) (pgk (QE i) (pgk Y (pgk X z)))))

@[expose] noncomputable def ncv4 (X Y F b : Nat) : Bool :=
  bAnd(ncvAt X Y 0 (fl F b), bAnd(ncvAt X Y 1 (fl F (Nat.add b 1)),
    bAnd(ncvAt X Y 2 (fl F (Nat.add b 2)), ncvAt X Y 3 (fl F (Nat.add b 3)))))

@[expose] noncomputable def SK (s : Nat) : Nat := SuzRgT (Nat.mul 4 s)

@[expose] noncomputable def stK (s R F : Nat) : Bool :=
  strictB (Nat.add 9 (Nat.mul 6 s)) fun b => strictB (fl F b) fun k =>
    strictB (fl F (Nat.add b 1)) fun a =>
    bIf(Nat.beq k 1, bAnd(Nat.blt a 1782,
        Bool.not (Nat.beq (pgk R (pgk R a)) (pgk (SuzRgV (Nat.add 1 s)) a))),
      bIf(Nat.beq k 0, bAnd(Nat.blt a 2,
          ncv4 (SuzRgV (Nat.add 3 (Nat.add (Nat.mul 2 s) a))) R F (Nat.add b 2)),
        bAnd(Nat.blt a 4, Nat.beq R (pc (SK s) (QE a)))))

@[expose] noncomputable def cellR (c j F : Nat) : Bool :=
  strictB (SuzRgU c) fun U => strictB (QE j) fun Q =>
    bIf(Nat.beq (fl F 0) 0,
      bAnd(Nat.blt (fl F 1) 1782, Bool.not (Nat.beq (pgk U (pgk Q (pgk W (fl F 1))))
        (pgk W (pgk U (pgk Q (fl F 1)))))),
      strictB (pc U Q) fun R => bAnd(Nat.beq (pc R W) (pc W R),
        bAnd(bAnd(Nat.blt (fl F 1) 256, bAnd(Nat.blt (fl F 2) 4,
            Nat.beq R (pc (SuzRgPT (fl F 1)) (QE (fl F 2))))),
          bAnd(bIf(inV c j, true, bAnd(Nat.blt (fl F 3) 8,
              bAnd(ncAt R (SuzRgT (fl F 3)) (fl F 4), ncv4 R (SuzRgV 0) F 5))),
            bAnd(stK 0 R F, stK 1 R F)))))

@[expose] noncomputable def cellK (c j : Nat) : Bool :=
  strictB (pg 256 (mask 256) (SuzRgE c) j) fun F => cellR c j F

@[expose] noncomputable def cellSl (s : Nat) : Bool :=
  strictB (Nat.shiftRight s 3) fun c => allBlk (Nat.mul 16 (Nat.land s 7)) (fun j => cellK c j) 16

@[expose] noncomputable def ptK (m : Nat) : Nat :=
  (List.range 8).foldl (fun acc i => if m.testBit i then pc acc (SuzRgT i) else acc) Id

@[expose] noncomputable def ptSl (s : Nat) : Bool :=
  allBlk (Nat.mul 16 s) (fun m => Nat.beq (SuzRgPT m) (ptK m)) 16

@[expose] noncomputable def utK (c : Nat) : Nat :=
  nIf(Nat.beq (CFSG.Sporadic.SuzRecog.RigidL2.rigUFix.getD c 0) 1,
    pc (qProdK 2) (cWK (CFSG.Sporadic.SuzRecog.RigidL2.rigUWords.getD c [])),
    cWK (CFSG.Sporadic.SuzRecog.RigidL2.rigUWords.getD c []))

@[expose] noncomputable def gen (i : Nat) : Nat × List Nat × Nat × Nat :=
  CFSG.Sporadic.SuzRecog.RigidL2.rigGens.getD i (0, [], 0, 0)

@[expose] noncomputable def gam (s g : Nat) : List Nat :=
  (CFSG.Sporadic.SuzRecog.RigidL2.rigGam.getD s []).getD g []

@[expose] noncomputable def perpK (v : Nat) : Bool :=
  Bool.not (Nat.blt 0 (Nat.land (CFSG.KS.Mathieu.nget SuzRgN 0) (Nat.shiftLeft 1 v)))

@[expose] noncomputable def uTestK (X : Nat) : Bool :=
  bAnd(Nat.beq (g7 X 1) 1, allN 64 fun v => bIf(perpK v, strictB (g7 X v) fun a =>
    bIf(Nat.beq a v, true, Nat.beq a (Nat.xor v 1)), true))

@[expose] noncomputable def agreeK (X M : Nat) : Bool :=
  allN 64 fun v => bIf(perpK v, strictB (g7 X v) fun a => strictB (g7 M v) fun b =>
    bIf(Nat.beq a b, true, Nat.beq a (Nat.xor b 1)), true)

@[expose] noncomputable def ucSl (s : Nat) : Bool :=
  allN 1620 fun d => strictB (Nat.add (Nat.mul 1620 s) d) fun i =>
    bIf(uTestK (SuzFbE.T i), SuzFb.memK SuzRgUP i, true)

@[expose] noncomputable def bfSl (s : Nat) : Bool :=
  strictB (SuzRgBW s) fun B => allN 320 fun d =>
    strictB (SuzFbE.T (Nat.add (Nat.mul 320 s) d)) fun X =>
    bIf(Nat.beq (g7 X 1) 1, strictB (pg 6 (mask 6) B d) fun k =>
      bAnd(Nat.blt k 60, agreeK X (SuzRgM k)), true)

@[expose] noncomputable def bvec (v : Nat) : List Nat := 1 :: (List.range 8).map fun k => g7 (SuzRgM k) v

@[expose] noncomputable def irK (v : Nat) : Bool :=
  bIf(perpK v, bIf(Nat.blt 1 v, strictB (SuzRgIW v) fun B => allN 64 fun u =>
    bIf(perpK u, strictB (pg 9 (mask 9) B u) fun m =>
      bAnd(Nat.blt m 512, CFSG.Sporadic.SuzRecog.RigidL2.rigXor (bvec v) m == u), true), true), true)

end CertificateChecks.KernelSpor.SuzRg

end
