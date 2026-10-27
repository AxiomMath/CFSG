module

public import Certificates.Kernel.Sporadic.OddCore.SuzFbD
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EG
public import Certificates.Kernel.Sporadic.OddCore.SuzAB

public section

namespace CertificateChecks.KernelSpor.SuzFb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.PEnum
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzMGF
  CertificateChecks.KernelSpor.SuzC1EG

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "pgk" => pg 11 (mask 11)
local notation "Id" => pidn 1782 11
local notation "g7" => pg 7 (mask 7)

@[expose] noncomputable def W : Nat := KernelLC.SuzB0QE 2

@[expose] noncomputable def WT : Nat := KernelLC.SuzB0QE 3

@[expose] noncomputable def pathW (PL : Nat → Nat) (fuel : Nat) : Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih i => Bool.rec (motive := fun _ => List Nat) (labOf PL i :: ih (parOf PL i)) []
      (Nat.beq i 0)) fuel

@[expose] noncomputable def ipos (q : Nat) : Nat := CFSG.KS.Mathieu.nget SuzFbIL q

@[expose] noncomputable def wq (q : Nat) : List Nat := pathW SuzFbE.PL 25920 (ipos q)

@[expose] noncomputable def lettersK (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun k _ ih => bAnd(Nat.blt k 10, ih)) w

@[expose] noncomputable def mWK (w : List Nat) : Nat :=
  wordTabK 64 7 (mask 7) (pidn 64 7) SuzABM w

@[expose] noncomputable def wordOK (q : Nat) : Bool :=
  strictB (ipos q) fun i => bAnd(Nat.blt i 25920,
    bAnd(Nat.beq (mWK (wq q)) (SuzFbE.T i), lettersK (wq q)))

@[expose] noncomputable def liftOK (q : Nat) : Bool :=
  bAnd(canonK 1782 11 (mask 11) (1782 * 11) (SuzFbL q), Nat.beq (SuzFbL q) (cWK (wq q)))

@[expose] noncomputable def liftSl (s : Nat) : Bool :=
  allBlk (Nat.mul 6 s) (fun q => bIf(Nat.blt q 76, liftOK q, true)) 6

@[expose] noncomputable def qeOK (j : Nat) : Bool :=
  bAnd(canonK 1782 11 (mask 11) (1782 * 11) (KernelLC.SuzB0QE j),
    Nat.beq (KernelLC.SuzB0QE j) (qEK j))

@[expose] noncomputable def qeSl (s : Nat) : Bool :=
  allBlk (Nat.mul 5 s) (fun j => bIf(Nat.blt j 128, qeOK j, true)) 5

@[expose] noncomputable def wOK : Bool :=
  bAnd(Nat.beq (qProdK 1) W, Nat.beq (pc W (SuzInvT1.F 0)) WT)

@[expose] noncomputable def kindRes (S : Nat) : Nat :=
  nIf(bIf(Nat.beq S W, true, Nat.beq S WT), 1, nIf(Nat.beq S Id, 2, 3))

@[expose] noncomputable def kindOK (X j e : Nat) : Bool :=
  strictB (KernelLC.SuzB0QE j) fun Q => strictB (Nat.shiftRight e 2) fun c =>
    bIf(Nat.beq c 0,
      strictB (pc X Q) fun Y => bAnd(Nat.beq (pc Y W) (pc W Y),
        Nat.beq (Nat.land e 3) (kindRes (pc Y Y))),
      strictB (Nat.sub c 1) fun p => bAnd(Nat.blt p 1782, bAnd(Nat.beq (Nat.land e 3) 0,
        Bool.not (Nat.beq (pgk X (pgk Q (pgk W p))) (pgk W (pgk X (pgk Q p)))))))

@[expose] noncomputable def kE (q j : Nat) : Nat := pg 13 (mask 13) (SuzFbW q) j

@[expose] noncomputable def kindSl (s : Nat) : Bool :=
  strictB (Nat.shiftRight s 4) fun q => strictB (SuzFbL q) fun X =>
    allBlk (Nat.mul 8 (Nat.land s 15)) (fun j => kindOK X j (kE q j)) 8

@[expose] noncomputable def conjTK (R G S : Nat) : Bool :=
  allN 64 fun y => Nat.beq (g7 R (g7 G y)) (g7 G (g7 S y))

@[expose] noncomputable def LB : Nat := SuzAB.wordK CFSG.Sporadic.SuzRecog.lBWord

@[expose] noncomputable def cw (q : Nat) : Nat := CFSG.KS.Mathieu.nget SuzFbCL q

@[expose] noncomputable def conjPos (q : Nat) : Bool :=
  strictB (cw q) fun c => bIf(Nat.beq c 0, true, bAnd(Nat.blt (Nat.sub c 1) 25920,
    conjTK (SuzFbE.T (ipos q)) (SuzFbE.T (Nat.sub c 1)) LB))

@[expose] noncomputable def conjNeg (q : Nat) : Bool :=
  bIf(Nat.beq (cw q) 0,
    allN 25920 (fun c => Bool.not (conjTK (SuzFbE.T (ipos q)) (SuzFbE.T c) LB)), true)

@[expose] noncomputable def fixInvK (X : Nat) : Bool :=
  bAnd(Nat.beq (g7 X 1) 1, Nat.beq (pcomp 64 7 (mask 7) X X) (pidn 64 7))

@[expose] noncomputable def memK (L : List Nat) (i : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => bIf(Nat.beq x i, true, ih)) L

@[expose] noncomputable def invSl (s : Nat) : Bool :=
  allN 1620 fun d => strictB (Nat.add (Nat.mul 1620 s) d) fun i =>
    bIf(fixInvK (SuzFbE.T i), memK SuzFbIL i, Bool.not (memK SuzFbIL i))

@[expose] noncomputable def slP (s : Nat) : Bool :=
  penumSlK 64 7 (mask 7) (64 * 7) false SuzFbE.G SuzFbE.GI 10 SuzFbE.cnt SuzFbE.T SuzFbE.PL
    SuzFbE.POS SuzFbE.SRT SuzFbE.SRI (320 * s) 320

end CertificateChecks.KernelSpor.SuzFb

end
