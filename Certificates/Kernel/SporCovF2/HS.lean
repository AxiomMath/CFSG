module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.SporCov.Defs
public import Certificates.Data.Kernel.SporCov.F2Kit
public import Certificates.Data.Kernel.SporCov.PCl
public import Certificates.Kernel.VecCert.HS

#kc_repo #kc_json_gz CFSG.KD.SporCovF2.HS.F "Certificates/Kernel/SporCovF2/data/hs3.json.gz" 788
  136201982769585312
  (T : List Nat) (Y1 : List Nat) (Y2 : List Nat) (G1 : List Nat) (G2 : List Nat)
  (M : List (List Nat)) (C : List (List Nat)) (R : List (List Nat))

set_option Elab.async false

public section

namespace CFSG.KD.SporCovF2.HS

open CFSG.KC.SporCov CFSG.KC.M1F2 CertificateChecks.KernelVec.HS

@[expose] noncomputable def chk (E : List Nat → List Nat → Bool) : Bool :=
  clH E letL 3 F.T F.Y1 F.Y2 F.G1 F.G2 F.M 4 && allLt 4 (clL E F.Y1 F.Y2 3 F.M) &&
    stH letL F.R 2 && allLt 2 (stOK E F.M F.C F.R) && neOK E F.T && chW letL F.T

namespace Ck

theorem ok : kitF 20 MA MB 2 5 chk = true := by quickRfl

theorem bA : m1Bind csA 20 MA = true := by quickRfl

theorem bB : m1Bind csB 20 MB = true := by quickRfl

end Ck

end CFSG.KD.SporCovF2.HS

end
