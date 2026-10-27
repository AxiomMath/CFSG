module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporCovBase.SuzThreeData
public import Certificates.Data.Kernel.SporCov.BaseReg
public import Certificates.Data.Kernel.SporCov.PClM
public import Certificates.Data.Kernel.SporCov.CenL
public import Certificates.Kernel.Sporadic.SuzK.Data

set_option Elab.async false

public section

namespace CFSG.KD.SporCovBase.SuzThree

open CFSG.KC.SporCov CFSG.KS.PEnum CertificateChecks.KernelSpor.SuzK

@[expose] noncomputable def fBi (x : Nat) : Nat := r32 BE (r32 BE x)

@[expose] noncomputable def L : Nat → Bool := letRL 13

@[expose] noncomputable def Rs : List (List Nat) := [[0], [2]]

@[expose] noncomputable def tOf (c : Nat) : List Nat :=
  cond (Nat.beq c 0) F.t0 (cond (Nat.beq c 1) F.t1 F.t2)

@[expose] noncomputable def rcOK (E : List Nat → List Nat → Bool) : Bool :=
  allLt (lenW F.Rp) fun r => Nat.blt (nthN F.RCc r) 3 && chW L (nthW F.RCg r) &&
    cjOK E (tOf (nthN F.RCc r)) (nthW F.RCg r) (nthW F.Rp r)

@[expose] noncomputable def chk (E : List Nat → List Nat → Bool) (K : List Nat → Nat) : Bool :=
  allLt 7 (fun i => allLt 7 fun j => Nat.blt j i || pcR E 3 F.H F.R 7 i j) &&
    cenH E L F.H F.Rp F.Gs F.P 2187 && keyInc K F.H 7 3 F.P &&
    cenAll E 3 F.H 7 F.Rp F.Gs F.P F.T && rcOK E &&
    pclMOK E L F.H 7 F.nL0 F.nE0 2 F.t0 F.M0 F.Y0 F.H0 F.Yc0 F.C0 Rs F.K0 &&
    pclMOK E L F.H 7 F.nL1 F.nE1 2 F.t1 F.M1 F.Y1 F.H1 F.Yc1 F.C1 Rs F.K1 &&
    pclMOK E L F.H 7 F.nL2 F.nE2 2 F.t2 F.M2 F.Y2 F.H2 F.Yc2 F.C2 Rs F.K2

namespace Ck

theorem base : (Nat.beq (lenN F.bs) 6 && allLt 6 fun t =>
    Nat.beq (imB (r32 AL) (r32 AL) (r32 BE) fBi F.gw t) (lg (nthN F.bs t))) = true := by
  quickRfl

theorem ok : kitB 22880 (r32 AL) (r32 AL) (r32 BE) fBi lg tb F.Rg 13 1215 F.bs chk = true := by
  quickRfl

end Ck

end CFSG.KD.SporCovBase.SuzThree

end
