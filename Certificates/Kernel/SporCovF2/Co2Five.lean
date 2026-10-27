module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.SporCov.F2Kit
public import Certificates.Data.Kernel.SporCov.PCl
public import Certificates.Kernel.VecCert.Co2

#kc_repo #kc_json_gz CFSG.KD.SporCovF2.Co2Five.F "Certificates/Kernel/SporCovF2/data/co25.json.gz"
  12159 12418643195457423550
  (G1 : List Nat) (G2 : List Nat) (Z : List Nat) (E1 : Nat) (E2 : Nat) (T : List Nat)
  (M : List (List Nat)) (Y : List (List Nat)) (H : List (List Nat)) (Yc : List (List Nat))
  (K : List Nat) (C : List (List Nat)) (R : List (List Nat)) (A : List Nat) (W : List (List Nat))

set_option Elab.async false

public section

namespace CFSG.KD.SporCovF2.Co2Five

open CFSG.KC.SporCov CFSG.KC.M1F2 CertificateChecks.KernelVec.Co2

@[expose] noncomputable def chk (E : List Nat → List Nat → Bool) : Bool :=
  p3lOK E letL 5 F.E1 F.E2 4 2 2 F.G1 F.G2 F.Z F.T F.M F.Y F.H F.Yc F.C F.R F.K F.A F.W

namespace Ck

theorem ok : kitF 22 MA MB 2 5 chk = true := by quickRfl

theorem bA : m1Bind csA 22 MA = true := by quickRfl

theorem bB : m1Bind csB 22 MB = true := by quickRfl

end Ck

end CFSG.KD.SporCovF2.Co2Five

end
