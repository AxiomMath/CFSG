module

public import Certificates.Kernel.OmegaEight.SB3872B

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3872

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871

set_option maxHeartbeats 0 in
theorem fStep_0 : ∀ i < 7, fStep 0 i (fL 0 i) = fL 0 (i + 1) := by
  refine fStep_of (by norm_num) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_)
  · simp only [bkOK, bkBkt, bkKey, bkQ, bkTab, sMul_eqK, sInv_eqK, a9K_lin, sAutData, sCanon_get]
    interval_cases i <;> decide +kernel
  · interval_cases i <;> decide +kernel
  · simp only [fStepB, bkBkt, bkTgt, bkT, bkLhs, bkRhs, bkTab, sMul_eqK, sInv_eqK, a9K_lin,
      sAutData, sNfTab_get, sCanon_get, sConj, AutData.relOK, ys_fun, AutData.Pk]
    interval_cases i <;> decide +kernel

set_option maxHeartbeats 0 in
theorem fStep_1 : ∀ i < 7, fStep 1 i (fL 1 i) = fL 1 (i + 1) := by
  refine fStep_of (by norm_num) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_)
  · simp only [bkOK, bkBkt, bkKey, bkQ, bkTab, sMul_eqK, sInv_eqK, a9K_lin, sAutData, sCanon_get]
    interval_cases i <;> decide +kernel
  · interval_cases i <;> decide +kernel
  · simp only [fStepB, bkBkt, bkTgt, bkT, bkLhs, bkRhs, bkTab, sMul_eqK, sInv_eqK, a9K_lin,
      sAutData, sNfTab_get, sCanon_get, sConj, AutData.relOK, ys_fun, AutData.Pk]
    interval_cases i <;> decide +kernel

set_option maxHeartbeats 0 in
theorem fStep_2 : ∀ i < 7, fStep 2 i (fL 2 i) = fL 2 (i + 1) := by
  refine fStep_of (by norm_num) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_)
  · simp only [bkOK, bkBkt, bkKey, bkQ, bkTab, sMul_eqK, sInv_eqK, a9K_lin, sAutData, sCanon_get]
    interval_cases i <;> decide +kernel
  · interval_cases i <;> decide +kernel
  · simp only [fStepB, bkBkt, bkTgt, bkT, bkLhs, bkRhs, bkTab, sMul_eqK, sInv_eqK, a9K_lin,
      sAutData, sNfTab_get, sCanon_get, sConj, AutData.relOK, ys_fun, AutData.Pk]
    interval_cases i <;> decide +kernel

set_option maxHeartbeats 0 in
theorem fStep_3 : ∀ i < 7, fStep 3 i (fL 3 i) = fL 3 (i + 1) := by
  refine fStep_of (by norm_num) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_)
  · simp only [bkOK, bkBkt, bkKey, bkQ, bkTab, sMul_eqK, sInv_eqK, a9K_lin, sAutData, sCanon_get]
    interval_cases i <;> decide +kernel
  · interval_cases i <;> decide +kernel
  · simp only [fStepB, bkBkt, bkTgt, bkT, bkLhs, bkRhs, bkTab, sMul_eqK, sInv_eqK, a9K_lin,
      sAutData, sNfTab_get, sCanon_get, sConj, AutData.relOK, ys_fun, AutData.Pk]
    interval_cases i <;> decide +kernel

end CertificateChecks.KernelO8.SB3872

end
