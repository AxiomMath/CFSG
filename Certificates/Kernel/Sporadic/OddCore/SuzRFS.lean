module

public import Certificates.Kernel.Sporadic.OddCore.SuzRFD
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EG
public import CFSG.Sporadic.SuzRecog.LocalRFusionGenTests

public section

namespace CertificateChecks.KernelSpor.SuzRF

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzMGF
  CertificateChecks.KernelSpor.SuzC1EG

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "pgk" => pg 11 (mask 11)
local notation "Id" => pidn 1782 11

@[expose] noncomputable def wg (F : Nat → Nat) (i : Nat) : Nat := CFSG.KS.Row.rg 32 (mask 32) F 0 i

@[expose] noncomputable def L4 : Nat := cWK CFSG.Sporadic.SuzRecog.LocalR.lambda4Word

@[expose] noncomputable def OT (i : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) SuzRFO0.T (fun j _ =>
    Nat.rec (motive := fun _ => Nat → Nat) SuzRFO1.T (fun j _ =>
      Nat.rec (motive := fun _ => Nat → Nat) SuzRFO2.T (fun _ _ => SuzRFO3.T) j) j) i

@[expose] noncomputable def OC (i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) SuzRFO0.cnt (fun j _ =>
    Nat.rec (motive := fun _ => Nat) SuzRFO1.cnt (fun j _ =>
      Nat.rec (motive := fun _ => Nat) SuzRFO2.cnt (fun _ _ => SuzRFO3.cnt) j) j) i

@[expose] noncomputable def covK (X c : Nat) : Bool :=
  bIf(Nat.beq c 0, Nat.beq X Id,
    bIf(Nat.blt c 2048,
      strictB (Nat.sub c 1) fun p => bAnd(Nat.blt p 1782, Bool.not (Nat.beq (pgk X (pgk X p)) p)),
      strictB (Nat.div (Nat.sub c 2048) 8192) fun i => strictB (Nat.mod (Nat.sub c 2048) 8192)
        fun q => bAnd(Nat.blt i 4, bAnd(Nat.blt q (OC i), Nat.beq (OT i q) X))))

@[expose] noncomputable def comK (X e : Nat) : Bool :=
  bIf(Nat.beq e 0, Nat.beq (pc X L4) (pc L4 X),
    strictB (Nat.sub e 1) fun p => bAnd(Nat.blt p 1782,
      Bool.not (Nat.beq (pgk X (pgk L4 p)) (pgk L4 (pgk X p)))))

@[expose] noncomputable def wSl (s : Nat) : Bool :=
  allBlk (Nat.mul 32 s) (fun k => strictB (SuzRFS.T k) fun X =>
    bAnd(covK X (wg SuzRFWC k), comK X (wg SuzRFWV k))) 32

@[expose] noncomputable def VT (j : Nat) : Nat := SuzRFS.T (CFSG.KS.Mathieu.nget SuzRFV j)

@[expose] noncomputable def p4 (X : Nat) : Nat := strictN (pc X X) fun Y => pc Y Y

@[expose] noncomputable def p4OK (X : Nat) : Bool :=
  strictB (p4 X) fun Z => bIf(Nat.beq Z Id, true, Nat.beq Z (SuzInvT1.F 0))

@[expose] noncomputable def pSl (s : Nat) : Bool := allBlk (Nat.mul 16 s) (fun j => p4OK (VT j)) 16

@[expose] noncomputable def oSl3 (s : Nat) : Bool :=
  penumSlK 1782 11 (mask 11) (1782 * 11) true SuzRFO3.G SuzRFO3.GI 2 SuzRFO3.cnt SuzRFO3.T
    SuzRFO3.PL SuzRFO3.POS SuzRFO3.SRT SuzRFO3.SRI (6 * s) 6

@[expose] noncomputable def oSl2 (s : Nat) : Bool :=
  penumSlK 1782 11 (mask 11) (1782 * 11) true SuzRFO2.G SuzRFO2.GI 2 SuzRFO2.cnt SuzRFO2.T
    SuzRFO2.PL SuzRFO2.POS SuzRFO2.SRT SuzRFO2.SRI (6 * s) 6

@[expose] noncomputable def oSl1 (s : Nat) : Bool :=
  penumSlK 1782 11 (mask 11) (1782 * 11) true SuzRFO1.G SuzRFO1.GI 2 SuzRFO1.cnt SuzRFO1.T
    SuzRFO1.PL SuzRFO1.POS SuzRFO1.SRT SuzRFO1.SRI (6 * s) 6

@[expose] noncomputable def oSl0 (s : Nat) : Bool :=
  penumSlK 1782 11 (mask 11) (1782 * 11) true SuzRFO0.G SuzRFO0.GI 2 SuzRFO0.cnt SuzRFO0.T
    SuzRFO0.PL SuzRFO0.POS SuzRFO0.SRT SuzRFO0.SRI (6 * s) 6

@[expose] noncomputable def sSl (s : Nat) : Bool :=
  penumSlK 1782 11 (mask 11) (1782 * 11) false SuzRFS.G SuzRFS.GI 4 SuzRFS.cnt SuzRFS.T SuzRFS.PL
    SuzRFS.POS SuzRFS.SRT SuzRFS.SRI (8 * s) 8

@[expose] noncomputable def lamK (i : Nat) : Nat :=
  nIf(Nat.beq i 0, SuzInvT1.F 0, nIf(Nat.beq i 1, qProdK 1, nIf(Nat.beq i 2, cWK [1], L4)))

@[expose] noncomputable def sK (j : Nat) : Nat :=
  nIf(Nat.beq j 0, KernelLC.SuzB0Q.F 0, nIf(Nat.beq j 1, cWK [6],
    nIf(Nat.beq j 2, cWK [7, 9, 2, 4], cWK [3, 6, 5, 7])))

@[expose] noncomputable def bindO (R : Nat) (G GI : Nat → Nat) (i : Nat) : Bool :=
  bAnd(Nat.beq R (lamK i), bAnd(Nat.beq (G 0) (SuzInvT1.F 20), bAnd(Nat.beq (G 1) (SuzInvT1.F 22),
    bAnd(invEqK 1782 11 (mask 11) (1782 * 11) (G 0) (GI 0),
    bAnd(invEqK 1782 11 (mask 11) (1782 * 11) (G 1) (GI 1),
    bAnd(canonK 1782 11 (mask 11) (1782 * 11) (GI 0), canonK 1782 11 (mask 11) (1782 * 11) (GI 1)))))))

@[expose] noncomputable def oWK (w : List Nat) : Nat :=
  wK (fun k => SuzInvT1.F (Nat.add 20 (Nat.mul 2 k))) w

@[expose] noncomputable def genK (k : Nat) : Bool :=
  bAnd((CFSG.Sporadic.SuzRecog.LocalR.cBackWords.getD k []).all (· < 2),
    Nat.beq (oWK (CFSG.Sporadic.SuzRecog.LocalR.cBackWords.getD k [])) (SuzInvT1.F (18 + k)))

end CertificateChecks.KernelSpor.SuzRF

end
