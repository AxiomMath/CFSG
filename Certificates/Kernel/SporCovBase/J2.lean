module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.SporCov.Defs
public import Certificates.Data.Kernel.SporCov.PCl
public import Certificates.Data.Kernel.SporCov.BaseKit
public import Certificates.Data.Kernel.Spor.PEnum
public import Certificates.Kernel.Sporadic.J2K.Data

#kc_repo #kc_json_gz CFSG.KD.SporCovBase.J2.F3 "Certificates/Kernel/SporCovBase/data/j23.json.gz" 4587
  2139876891572128306
  (G1 : List Nat) (G2 : List Nat) (Z : List Nat) (E1 : Nat) (E2 : Nat) (T : List Nat)
  (M : List (List Nat)) (Y : List (List Nat)) (H : List (List Nat)) (Yc : List (List Nat))
  (K : List Nat) (C : List (List Nat)) (R : List (List Nat)) (A : List Nat) (W : List (List Nat))

#kc_repo #kc_json_gz CFSG.KD.SporCovBase.J2.F5 "Certificates/Kernel/SporCovBase/data/j25.json.gz" 3257
  10842308748833330836
  (T : List Nat) (Y1 : List Nat) (Y2 : List Nat) (G1 : List Nat) (G2 : List Nat)
  (M : List (List Nat)) (C : List (List Nat)) (R : List (List Nat))

set_option Elab.async false

public section

namespace CFSG.KD.SporCovBase.J2

open CFSG.KC.SporCov CFSG.KS.PEnum CertificateChecks.KernelSpor.J2K

@[expose] noncomputable def bs : List Nat := [0, 4, 3, 1, 2, 6, 7, 8, 10, 11, 12, 13, 15, 17]

@[expose] noncomputable def E : List Nat → List Nat → Bool := eqB (r32 AL) (r32 AI) (r32 BE) (r32 BI) bs

@[expose] noncomputable def chk3 (E : List Nat → List Nat → Bool) : Bool :=
  p3lOK E letP 3 F3.E1 F3.E2 5 1 2 F3.G1 F3.G2 F3.Z F3.T F3.M F3.Y F3.H F3.Yc F3.C F3.R F3.K F3.A
    F3.W

@[expose] noncomputable def chk5 (E : List Nat → List Nat → Bool) : Bool :=
  clH E letP 5 F5.T F5.Y1 F5.Y2 F5.G1 F5.G2 F5.M 7 && allLt 7 (clL E F5.Y1 F5.Y2 5 F5.M) &&
    stH letP F5.R 2 && allLt 2 (stOK E F5.M F5.C F5.R) && neOK E F5.T && chW letP F5.T

namespace Ck

theorem ok3 : chk3 E = true := by quickRfl

theorem ok5 : chk5 E = true := by quickRfl

end Ck

end CFSG.KD.SporCovBase.J2

end
