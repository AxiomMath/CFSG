module

public import Certificates.Kernel.Sporadic.OddCore.SuzGlD
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EF
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EZ
public import CFSG.Sporadic.SuzRecog.B0GluingTests

public section

namespace CertificateChecks.KernelSpor.SuzGl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.PEnum
open CFSG.Sporadic.SuzRecog.B0Gluing CFSG.Sporadic.SuzRecog.B0GluingData
open CertificateChecks.KernelSpor

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "pgk" => pg 11 (mask 11)
local notation "g7" => pg 7 (mask 7)
local notation "T" => SuzC1ET.T
local notation "Id" => pidn 1782 11
local notation "W0" => SuzTwG 6

@[expose] noncomputable def fpL (F : Nat → Nat) (d y k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) d (fun j ih => nIf(Nat.beq (F j) y, j, ih)) k

@[expose] noncomputable def fpT (y : Nat) : Nat := fpL (fun j => pgk (T j) 0) 64 y 64

@[expose] noncomputable def fpY (X y : Nat) : Nat :=
  fpL (fun j => pgk (SuzGlY (Nat.add (Nat.mul 64 X) j)) 0) 64 y 64

@[expose] noncomputable def mulK (a b : Nat) : Nat :=
  nIf(bAnd(Nat.blt a 64, Nat.blt b 64), g7 (SuzGlM a) b, 0)

@[expose] noncomputable def invK (a : Nat) : Nat := nIf(Nat.blt a 64, g7 (SuzGlI 0) a, 0)

@[expose] noncomputable def cmK (a b : Nat) : Nat :=
  nIf(bAnd(Nat.blt a 64, Nat.blt b 64), g7 (SuzGlC a) b, 0)

@[expose] noncomputable def gK (i : Nat) : Nat := nIf(Nat.blt i 4, Nat.succ i, 0)

@[expose] noncomputable def chiK (v k : Nat) : Nat :=
  nIf(bAnd(Nat.blt v 15, Nat.blt k 64), g7 (SuzGlX v) k, 0)

@[expose] noncomputable def gamK (r k : Nat) : Nat :=
  nIf(bAnd(Nat.blt r 16, Nat.blt k 64), g7 (SuzGlG r) k, 0)

@[expose] noncomputable def gamIK (r k : Nat) : Nat :=
  nIf(bAnd(Nat.blt r 16, Nat.blt k 64), g7 (SuzGlGI r) k, 0)

@[expose] noncomputable def thK (i k : Nat) : Nat :=
  nIf(bAnd(Nat.blt i 36, Nat.blt k 64), g7 (SuzGlP i) k, 0)

@[expose] noncomputable def thIK (i k : Nat) : Nat :=
  nIf(bAnd(Nat.blt i 36, Nat.blt k 64), g7 (SuzGlPI i) k, 0)

@[expose] noncomputable def nAK (l k : Nat) : Nat :=
  nIf(bAnd(Nat.blt l 4, Nat.blt k 64), g7 (SuzGlA l) k, 0)

@[expose] noncomputable def cAK (X p : Nat) : Nat :=
  nIf(bAnd(Nat.blt X 2, Nat.blt p 64), g7 (SuzGlK X) p, 0)

@[expose] noncomputable def labT (k : Nat) : Nat := nIf(Nat.blt k 64, labOf SuzC1ET.PL k, 0)

@[expose] noncomputable def parT (k : Nat) : Nat := nIf(Nat.blt k 64, parOf SuzC1ET.PL k, 0)

@[expose] def zIL : Array Nat := #[0, 45, 53, 57]

@[expose] noncomputable def gammaGenK (r i : Nat) : Nat :=
  mulK (gK i) zIL[(gammaReps.getD r []).getD i 0]!

@[expose] noncomputable def chiRecK (v : Nat) : Bool :=
  bAnd(Nat.beq (g7 (SuzGlX v) 0) 0, allN 63 fun j => strictB (Nat.succ j) fun k =>
    bAnd(Nat.blt (parT k) k,
      Nat.beq (g7 (SuzGlX v) k) ((chiBit v (labT k) + g7 (SuzGlX v) (parT k)) % 2)))

@[expose] noncomputable def gamRecK (r : Nat) : Bool :=
  bAnd(Nat.beq (g7 (SuzGlG r) 0) 0, allN 63 fun j => strictB (Nat.succ j) fun k =>
    bAnd(Nat.blt (parT k) k,
      Nat.beq (g7 (SuzGlG r) k) (mulK (gammaGenK r (labT k)) (g7 (SuzGlG r) (parT k)))))

@[expose] noncomputable def radPosK (X : Nat) : Array Nat :=
  ((List.range 64).filter fun k =>
    cmK k (gK (2 * X)) == 0 && cmK k (gK (2 * X + 1)) == 0).toArray

@[expose] noncomputable def radK (X i : Nat) : Nat := (radPosK X)[i]!

@[expose] noncomputable def radIdxK (X e : Nat) : Nat :=
  nIf(bAnd(Nat.blt X 2, Nat.blt e 64), fpL (radK X) 16 e 16, 0)

@[expose] noncomputable def idxSl (a : Nat) : Bool :=
  allN 64 fun b => strictB (mulK a b) fun m => bAnd(Nat.blt m 64, Nat.beq (T m) (pc (T a) (T b)))

@[expose] noncomputable def r0K (q : Nat) : Nat :=
  nIf(Nat.beq q 0, Id, nIf(Nat.beq q 1, W0, nIf(Nat.beq q 2, SuzC1BT 11, SuzC1BT 12)))

@[expose] noncomputable def y0OK (m : Nat) : Bool :=
  Nat.beq (SuzGlY m) (pc (T (radK (Nat.div m 64) (Nat.div (Nat.mod m 64) 4))) (r0K (Nat.mod m 4)))

@[expose] noncomputable def y0Sl (s : Nat) : Bool := allBlk (Nat.mul 32 s) y0OK 32

@[expose] noncomputable def cAOK (m : Nat) : Bool :=
  strictB (Nat.div m 64) fun X => strictB (pc (pc (SuzGlW X) (SuzGlY m)) (SuzGlWI X)) fun C =>
    strictB (g7 (SuzGlK X) (Nat.mod m 64)) fun a => bAnd(Nat.blt a 64,
      bAnd(Nat.beq (fpY X (pgk C 0)) a, Nat.beq (SuzGlY (Nat.add (Nat.mul 64 X) a)) C))

@[expose] noncomputable def cASl (s : Nat) : Bool := allBlk (Nat.mul 32 s) cAOK 32

@[expose] noncomputable def nAOK (m : Nat) : Bool :=
  strictB (Nat.div m 64) fun l =>
    strictB (pc (pc (SuzGlN l) (T (Nat.mod m 64))) (SuzGlNI l)) fun Y =>
      strictB (fpT (pgk Y 0)) fun j =>
        Nat.beq (g7 (SuzGlA l) (Nat.mod m 64)) (nIf(bAnd(Nat.blt j 64, Nat.beq (T j) Y), j, 64))

@[expose] noncomputable def nASl (s : Nat) : Bool := allBlk (Nat.mul 32 s) nAOK 32

@[expose] noncomputable def memA (X : Nat) : Bool :=
  Bool.not (allN 12 fun j => Bool.not (Nat.beq (SuzC1EA.T j) X))

@[expose] noncomputable def rhoK (X : Nat) : Bool :=
  strictB (pc X X) fun C2 =>
    Bool.or (Bool.not (bAnd(Nat.beq (pc X C2) Id, bAnd(Bool.not (Nat.beq X Id),
      strictB (pc (pc X W0) C2) fun U => bAnd(Nat.beq (pc U W0) (pc W0 U),
        bAnd(Bool.not (Nat.beq U W0), Nat.beq (pc (pc X U) C2) (pc W0 U))))))) (memA X)

@[expose] noncomputable def rhoSl (s : Nat) : Bool :=
  allBlk (Nat.mul 16 s) (fun i => rhoK (SuzC1EQ.T i)) 16

end CertificateChecks.KernelSpor.SuzGl

end
