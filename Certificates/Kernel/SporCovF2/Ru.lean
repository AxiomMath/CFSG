module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.SporCov.F2Kit
public import Certificates.Data.Kernel.SporCov.PCl
public import Certificates.Kernel.VecCert.Ru

#kc_repo #kc_json_gz CFSG.KD.SporCovF2.Ru.F3 "Certificates/Kernel/SporCovF2/data/ru3.json.gz" 1688
  12238625855226554009
  (G1 : List Nat) (G2 : List Nat) (Z : List Nat) (E1 : Nat) (E2 : Nat) (T : List Nat)
  (M : List (List Nat)) (Y : List (List Nat)) (H : List (List Nat)) (Yc : List (List Nat))
  (K : List Nat) (C : List (List Nat)) (R : List (List Nat)) (GZ : List Nat)

#kc_repo #kc_json_gz CFSG.KD.SporCovF2.Ru.F5 "Certificates/Kernel/SporCovF2/data/ru5.json.gz" 1552
  4959379735725737710
  (G1 : List Nat) (G2 : List Nat) (Z : List Nat) (E1 : Nat) (E2 : Nat) (T : List Nat)
  (M : List (List Nat)) (Y : List (List Nat)) (H : List (List Nat)) (Yc : List (List Nat))
  (K : List Nat) (C : List (List Nat)) (R : List (List Nat)) (GZ : List Nat)

set_option Elab.async false

public section

namespace CFSG.KD.SporCovF2.Ru

open CFSG.KC.SporCov CFSG.KC.M1F2 CertificateChecks.KernelVec.Ru

@[expose] noncomputable def chk3 (E : List Nat → List Nat → Bool) : Bool :=
  p3cOK E letL 3 F3.E1 F3.E2 3 1 2 F3.G1 F3.G2 F3.Z F3.T F3.GZ F3.M F3.Y F3.H F3.Yc F3.C F3.R F3.K

@[expose] noncomputable def chk5 (E : List Nat → List Nat → Bool) : Bool :=
  p3cOK E letL 5 F5.E1 F5.E2 3 1 2 F5.G1 F5.G2 F5.Z F5.T F5.GZ F5.M F5.Y F5.H F5.Yc F5.C F5.R F5.K

namespace Ck

theorem ok3 : kitF 28 MA MB 2 4 chk3 = true := by quickRfl

theorem ok5 : kitF 28 MA MB 2 4 chk5 = true := by quickRfl

theorem bA : m1Bind csA 28 MA = true := by quickRfl

theorem bB : m1Bind csB 28 MB = true := by quickRfl

end Ck

end CFSG.KD.SporCovF2.Ru

end
