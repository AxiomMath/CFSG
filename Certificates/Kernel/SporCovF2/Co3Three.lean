module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.SporCov.F2Reg
public import Certificates.Data.Kernel.SporCov.PClM
public import Certificates.Data.Kernel.SporCov.CenL
public import Certificates.Kernel.VecCert.Co3

#kc_repo #kc_json_gz CFSG.KD.SporCovF2.Co3Three.F "Certificates/Kernel/SporCovF2/data/co33.json.gz"
  178381 11545974179171738793
  (Rg : List (List Nat)) (Ms : List Nat) (H : List (List Nat)) (R : List (List Nat))
  (P : List Nat) (T : List (List Nat)) (Rp : List (List Nat)) (Gs : List (List Nat))
  (M0 : List (List Nat)) (nL0 : Nat) (Y0 : List (List Nat)) (H0 : List (List Nat))
  (Yc0 : List (List Nat)) (K0 : List Nat) (nE0 : Nat) (C0 : List (List Nat))
  (M1 : List (List Nat)) (nL1 : Nat) (Y1 : List (List Nat)) (H1 : List (List Nat))
  (Yc1 : List (List Nat)) (K1 : List Nat) (nE1 : Nat) (C1 : List (List Nat))
  (M2 : List (List Nat)) (nL2 : Nat) (Y2 : List (List Nat)) (H2 : List (List Nat))
  (Yc2 : List (List Nat)) (K2 : List Nat) (nE2 : Nat) (C2 : List (List Nat))

set_option Elab.async false

public section

namespace CFSG.KD.SporCovF2.Co3Three

open CFSG.KC.SporCov CFSG.KC.M1F2 CertificateChecks.KernelVec.Co3

@[expose] noncomputable def nR : Nat := lenW F.Rg

@[expose] noncomputable def L : Nat → Bool := letRL nR

@[expose] noncomputable def Rs : List (List Nat) := [[0], [2]]

@[expose] noncomputable def chk (E : List Nat → List Nat → Bool) (K : List Nat → Nat) : Bool :=
  allLt 7 (fun i => allLt 7 fun j => Nat.blt j i || pcR E 3 F.H F.R 7 i j) &&
    cenH E L F.H F.Rp F.Gs F.P 2187 && keyInc K F.H 7 3 F.P &&
    cenAll E 3 F.H 7 F.Rp F.Gs F.P F.T &&
    pclMOK E L F.H 7 F.nL0 F.nE0 2 (nthW F.Rp 0) F.M0 F.Y0 F.H0 F.Yc0 F.C0 Rs F.K0 &&
    pclMOK E L F.H 7 F.nL1 F.nE1 2 (nthW F.Rp 1) F.M1 F.Y1 F.H1 F.Yc1 F.C1 Rs F.K1 &&
    pclMOK E L F.H 7 F.nL2 F.nE2 2 (nthW F.Rp 2) F.M2 F.Y2 F.H2 F.Yc2 F.C2 Rs F.K2

namespace Ck

theorem ok : kitR 22 MA MB 3 4 F.Ms F.Rg nR chk = true := by quickRfl

end Ck

end CFSG.KD.SporCovF2.Co3Three

end
