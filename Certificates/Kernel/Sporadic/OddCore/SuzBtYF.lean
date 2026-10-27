module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtXF
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtYF

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzBtXF

local notation "pg4" => pg 4 (mask 4)

@[expose] noncomputable def bt (m k : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight m k) 1) 1

@[expose] noncomputable def cmb (v0 v1 v2 v3 m : Nat) : Nat :=
  Nat.xor (nIf(bt m 0, v0, 0)) (Nat.xor (nIf(bt m 1, v1, 0))
    (Nat.xor (nIf(bt m 2, v2, 0)) (nIf(bt m 3, v3, 0))))

@[expose] noncomputable def indep (a b c : Nat) : Bool :=
  allN 15 (fun m => Bool.not (Nat.beq (cmb 1 a b c (Nat.succ m)) 0))

@[expose] noncomputable def tab (a b c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun m ih => Nat.add ih
    (Nat.shiftLeft (cmb a b c (Nat.xor (Nat.xor 1 a) (Nat.xor b c)) m)
      (Nat.mul 4 (cmb 1 a b c m)))) 16

@[expose] noncomputable def TT (s : Nat) : Nat :=
  nIf(Nat.beq s 0, 18364758544493064720, nIf(Nat.beq s 1, 17274361803683611920,
    nIf(Nat.beq s 2, 9929781798390354960, 11001113007572198160)))

@[expose] noncomputable def img (T w p : Nat) : Nat :=
  pg4 (TT (Nat.mod w 4)) (pw T (Nat.mod (Nat.div w 4) 5) (pg4 (TT (Nat.div w 20)) p))

@[expose] noncomputable def key (T w : Nat) : Nat :=
  Nat.add (img T w 1) (Nat.add (Nat.shiftLeft (img T w 2) 4) (Nat.shiftLeft (img T w 4) 8))

@[expose] noncomputable def addK (st k : Nat) : Nat :=
  nIf(bt st (Nat.add k 8), st, Nat.add st (Nat.add 1 (Nat.shiftLeft 1 (Nat.add k 8))))

@[expose] noncomputable def famCnt (T : Nat) : Nat :=
  Nat.land (Nat.rec (motive := fun _ => Nat) 0
    (fun w ih => strictN ih (fun st => addK st (key T w))) 80) 255

@[expose] noncomputable def inX (T : Nat) : Bool :=
  Bool.not (bAnd(Bool.not (memK SuzBtX0.K 60 T), bAnd(Bool.not (memK SuzBtX1.K 60 T),
    bAnd(Bool.not (memK SuzBtX2.K 60 T), Bool.not (memK SuzBtX3.K 60 T)))))

@[expose] noncomputable def chkA (B : Nat) (X : Nat → Bool) (a : Nat) : Bool :=
  allN 15 (fun b => allN 15 (fun c => bIf(indep a (Nat.succ b) (Nat.succ c),
    strictB (tab a (Nat.succ b) (Nat.succ c)) (fun T =>
      bIf(Nat.blt B (famCnt T), true, X T)), true)))

theorem kY1 : chkA 60 inX 1 = true := by quickRfl
theorem kY2 : chkA 60 inX 2 = true := by quickRfl
theorem kY3 : chkA 60 inX 3 = true := by quickRfl
theorem kY4 : chkA 60 inX 4 = true := by quickRfl
theorem kY5 : chkA 60 inX 5 = true := by quickRfl
theorem kY6 : chkA 60 inX 6 = true := by quickRfl
theorem kY7 : chkA 60 inX 7 = true := by quickRfl
theorem kY8 : chkA 60 inX 8 = true := by quickRfl
theorem kY9 : chkA 60 inX 9 = true := by quickRfl
theorem kY10 : chkA 60 inX 10 = true := by quickRfl
theorem kY11 : chkA 60 inX 11 = true := by quickRfl
theorem kY12 : chkA 60 inX 12 = true := by quickRfl
theorem kY13 : chkA 60 inX 13 = true := by quickRfl
theorem kY14 : chkA 60 inX 14 = true := by quickRfl
theorem kY15 : chkA 60 inX 15 = true := by quickRfl

end CertificateChecks.KernelSpor.SuzBtYF

end
