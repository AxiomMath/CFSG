module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.SporCov.Defs
public import Certificates.Data.Kernel.SporCov.PCl
public import Certificates.Data.Kernel.SporCov.BaseKit
public import Certificates.Data.Kernel.Spor.PEnum
public import Certificates.Kernel.Sporadic.SuzK.Data

#kc_repo #kc_json_gz CFSG.KD.SporCovBase.Suz.F "Certificates/Kernel/SporCovBase/data/suz5.json.gz" 2307
  4803519142163316727
  (T : List Nat) (Y1 : List Nat) (Y2 : List Nat) (G1 : List Nat) (G2 : List Nat)
  (M : List (List Nat)) (C : List (List Nat)) (R : List (List Nat))

set_option Elab.async false

public section

namespace CFSG.KD.SporCovBase.Suz

open CFSG.KC.SporCov CFSG.KS.PEnum CertificateChecks.KernelSpor.SuzK

@[expose] noncomputable def bs : List Nat := [0, 1, 2, 3, 4, 5]

@[expose] noncomputable def fBi (x : Nat) : Nat := r32 BE (r32 BE x)

@[expose] noncomputable def E : List Nat → List Nat → Bool := eqB (r32 AL) (r32 AL) (r32 BE) fBi bs

@[expose] noncomputable def chk (E : List Nat → List Nat → Bool) : Bool :=
  clH E letP 5 F.T F.Y1 F.Y2 F.G1 F.G2 F.M 4 && allLt 4 (clL E F.Y1 F.Y2 3 F.M) &&
    stH letP F.R 2 && allLt 2 (stOK E F.M F.C F.R) && neOK E F.T && chW letP F.T

namespace Ck

theorem ok : chk E = true := by quickRfl

end Ck

end CFSG.KD.SporCovBase.Suz

end
