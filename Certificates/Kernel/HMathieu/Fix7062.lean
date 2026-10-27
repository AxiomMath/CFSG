
module

public import Certificates.Kernel.HMathieu.T22
public import Certificates.Kernel.HMathieu.T23
public import Certificates.Kernel.HMathieu.T24
public import Certificates.Data.Kernel.HMathieu.FixCert
public import CFSG.Quasithin.Background.HMathieuCodeInvInputs
public import CFSG.Quasithin.Background.HMathieuFacts24Inputs
public import CFSG.Quasithin.Background.HMathieuCentInputs
public meta import CFSG.Certificates.Kernel.Common.JsonGz
public meta import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

public section

#kc_repo #kc_json_gz CertificateChecks.KernelHMathieu.Fix7062
  "Certificates/Kernel/HMathieu/data/FixCert.json.gz" 3938 7272315038100942511
  (J22 : List (List Nat)) (J23 : List (List Nat)) (K23 : List (List Nat))
  (J24 : List (List Nat)) (J4 : List (List Nat)) (K4 : List (List Nat))

namespace CertificateChecks.KernelHMathieu.Fix7062

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu

@[expose] def mats4 : List (List Nat) :=
  [matOf 11 (act11 inv23Arr), matOf 11 (actC11 inv23Arr), matOf 11 (actC11 inv24Arr)]

theorem c22 : allImg 10 3 (T22.Md.take 71) J22 = true := by decide +kernel

theorem c23 : allImg 11 4 (T23.Md.take 35) J23 = true ∧ allKer 11 7 (T23.Md.take 35) K23 = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
theorem c24 : allImg 11 4 (T24.Md.take 191) J24 = true := by decide +kernel

theorem c4 : allImg 11 4 mats4 J4 = true ∧ allKer 11 7 mats4 K4 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem plain4 : inAutOK inv23Arr = true ∧ (∀ i < 24, inv23Arr[inv23Arr[i]!]! = i) ∧
    inv23Arr[0]! = 0 ∧ inv23Arr[1]! ≠ 1 := by decide +kernel

end CertificateChecks.KernelHMathieu.Fix7062

end
