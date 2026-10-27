module

public import Certificates.Kernel.Sporadic.OddCore.SuzPairD
public import Certificates.Kernel.Sporadic.OddCore.SuzRFS
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporSuzInputs

public section

namespace CertificateChecks.KernelSpor.SuzPair

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzRF

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "pgk" => pg 11 (mask 11)
local notation "Id" => pidn 1782 11
local notation "T1" => SuzInvT1.F 0

@[expose] noncomputable def neC (X Y p : Nat) : Bool :=
  Bool.not (Nat.beq (pgk X (pgk Y p)) (pgk Y (pgk X p)))

@[expose] noncomputable def neZ (X Y q : Nat) : Bool :=
  Bool.not (Nat.beq (pgk X (pgk Y q)) (pgk T1 (pgk Y (pgk X q))))

@[expose] noncomputable def zK (X e : Nat) : Bool :=
  bIf(Nat.beq e 0, allN 4 (fun j => Nat.beq (pc X (SuzRFS.G j)) (pc (SuzRFS.G j) X)),
    strictB (Nat.sub e 1) fun c => strictB (Nat.div c 2048) fun j =>
      strictB (Nat.mod c 2048) fun p =>
        bAnd(Nat.blt j 4, bAnd(Nat.blt p 1782, neC X (SuzRFS.G j) p)))

@[expose] noncomputable def z2K (X e : Nat) : Bool :=
  bIf(Nat.beq e 0, allN 4 (fun j => Nat.beq (pc X (SuzRFS.G j)) (pc (SuzRFS.G j) X) ||
      Nat.beq (pc X (SuzRFS.G j)) (pc T1 (pc (SuzRFS.G j) X))),
    strictB (Nat.sub e 1) fun c => strictB (Nat.div c 4194304) fun j =>
      strictB (Nat.mod c 4194304) fun r => strictB (Nat.div r 2048) fun p =>
        strictB (Nat.mod r 2048) fun q =>
          bAnd(Nat.blt j 4, bAnd(Nat.blt p 1782, bAnd(Nat.blt q 1782,
            bAnd(neC X (SuzRFS.G j) p, neZ X (SuzRFS.G j) q)))))

@[expose] noncomputable def w75343Sl (s : Nat) : Bool :=
  allBlk (Nat.mul 32 s) (fun k => strictB (SuzRFS.T k) fun X =>
    bAnd(zK X (wg SuzPairWZ k), z2K X (wg SuzPairW2 k))) 32

@[expose] noncomputable def ltK (G GI : Nat → Nat) (z : Int) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun n => nIf(Nat.beq n 0, GI 0, G (Nat.sub n 1)))
    (fun m => GI m) z

@[expose] noncomputable def iwK (G GI : Nat → Nat) (w : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) Id (fun z _ ih => pc (ltK G GI z) ih) w

@[expose] noncomputable def abK (j : Nat) : Nat := nIf(Nat.beq j 0, Suz2306.B0, Suz2306.B1)

@[expose] noncomputable def abIK (j : Nat) : Nat := nIf(Nat.beq j 0, SuzPairT 0, SuzPairT 1)

@[expose] noncomputable def cgK (j : Nat) : Nat :=
  nIf(Nat.beq j 0, SuzInvT1.F 20, nIf(Nat.beq j 1, SuzInvT1.F 22, SuzPairT 4))

@[expose] noncomputable def cgIK (j : Nat) : Nat :=
  nIf(Nat.beq j 0, SuzPairT 2, nIf(Nat.beq j 1, SuzPairT 3, SuzPairT 5))

@[expose] noncomputable def inVK (G X : Nat) : Bool :=
  Nat.beq (pc G X) (pc (SuzRFS.T 174) G) ||
    (Nat.beq (pc G X) (pc (SuzRFS.T 8113) G) || (Nat.beq (pc G X) (pc (SuzRFS.T 8149) G) || false))

end CertificateChecks.KernelSpor.SuzPair

end
