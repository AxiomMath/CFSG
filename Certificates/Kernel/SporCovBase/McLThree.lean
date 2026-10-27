module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporCovBase.McLThreeData
public import Certificates.Data.Kernel.SporCov.BaseReg
public import Certificates.Data.Kernel.SporCov.PClM
public import Certificates.Data.Kernel.SporCov.CenL
public import Certificates.Kernel.Sporadic.McLK.Data

set_option Elab.async false

public section

namespace CFSG.KD.SporCovBase.McLThree

open CFSG.KC.SporCov CFSG.KS.PEnum CertificateChecks.KernelSpor.McLK

@[expose] noncomputable def Q : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 26]

@[expose] noncomputable def L : Nat → Bool := letRL 12

@[expose] noncomputable def Rs : List (List Nat) := [[0], [2]]

@[expose] noncomputable def tOf (c : Nat) : List Nat := cond (Nat.beq c 0) F.t0 F.t1

@[expose] noncomputable def rcOK (E : List Nat → List Nat → Bool) : Bool :=
  allLt (lenW F.Rp) fun r => Nat.blt (nthN F.RCc r) 2 && chW L (nthW F.RCg r) &&
    cjOK E (tOf (nthN F.RCc r)) (nthW F.RCg r) (nthW F.Rp r)

@[expose] noncomputable def chk (E : List Nat → List Nat → Bool) (K : List Nat → Nat) : Bool :=
  allLt 6 (fun i => allLt 6 fun j => Nat.blt j i || pcR E 3 F.H F.R 6 i j) &&
    cenH E L F.H F.Rp F.Gs F.P 729 && keyInc K F.H 6 3 F.P &&
    cenAll E 3 F.H 6 F.Rp F.Gs F.P F.T && rcOK E &&
    pclMOK E L F.H 6 F.nL0 F.nE0 2 F.t0 F.M0 F.Y0 F.H0 F.Yc0 F.C0 Rs F.K0 &&
    pclMOK E L F.H 6 F.nL1 F.nE1 2 F.t1 F.M1 F.Y1 F.H1 F.Yc1 F.C1 Rs F.K1

namespace Ck

theorem base : (Nat.beq (lenN F.bs) 21 && allLt 21 fun t =>
    Nat.beq (lg (nthN F.bs t)) (nthN Q t)) = true := by
  quickRfl

theorem ok : kitB 275 (r32 AL) (r32 AL) (r32 BE) (r32 BI) lg tb F.Rg 12 274 F.bs chk = true := by
  quickRfl

end Ck

end CFSG.KD.SporCovBase.McLThree

end
