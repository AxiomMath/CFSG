module

public import Certificates.Kernel.OmegaEight.SB3872L1

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3872

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871

set_option maxHeartbeats 0 in
theorem fStep_4 : ∀ i < 7, fStep 4 i (fL 4 i) = fL 4 (i + 1) := by
  intro i hi
  simp only [fStep, sMul_eqK, sInv_eqK, a9K_lin, sAutData, sNfTab_get, sCanon_get, sConj,
    AutData.relOK, ys_fun, AutData.Pk]
  interval_cases i <;> decide +kernel

set_option maxHeartbeats 0 in
theorem fStep_5 : ∀ i < 7, fStep 5 i (fL 5 i) = fL 5 (i + 1) := by
  intro i hi
  simp only [fStep, sMul_eqK, sInv_eqK, a9K_lin, sAutData, sNfTab_get, sCanon_get, sConj,
    AutData.relOK, ys_fun, AutData.Pk]
  interval_cases i <;> decide +kernel

set_option maxHeartbeats 0 in
theorem fStep_6 : ∀ i < 7, fStep 6 i (fL 6 i) = fL 6 (i + 1) := by
  intro i hi
  simp only [fStep, sMul_eqK, sInv_eqK, a9K_lin, sAutData, sNfTab_get, sCanon_get, sConj,
    AutData.relOK, ys_fun, AutData.Pk]
  interval_cases i <;> decide +kernel

set_option maxHeartbeats 0 in
theorem fStep_7 : ∀ i < 7, fStep 7 i (fL 7 i) = fL 7 (i + 1) := by
  intro i hi
  simp only [fStep, sMul_eqK, sInv_eqK, a9K_lin, sAutData, sNfTab_get, sCanon_get, sConj,
    AutData.relOK, ys_fun, AutData.Pk]
  interval_cases i <;> decide +kernel

end CertificateChecks.KernelO8.SB3872

end
