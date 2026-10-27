module

public import Certificates.Kernel.OmegaEight.SB3872
public import Certificates.Kernel.OmegaEight.SB3872FData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3872

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871

@[expose] def fL (k i : ℕ) : List (List ℕ) := (fLit.getD k []).getD i []

@[expose] def fStep (k i : ℕ) (acc : List (List ℕ)) : List (List ℕ) :=
  acc.flatMap fun ds => ((sAutData.R k i).filter fun d =>
    sAutData.relOK sMul sInv k i (ds ++ [d])).map fun d => ds ++ [d]

set_option maxHeartbeats 0 in
theorem fStep_0 : ∀ i < 7, fStep 0 i (fL 0 i) = fL 0 (i + 1) := by
  intro i hi
  simp only [fStep, sMul_eqK, sInv_eqK, a9K_lin, sAutData, sNfTab_get, sCanon_get, sConj,
    AutData.relOK, ys_fun, AutData.Pk]
  interval_cases i <;> decide +kernel

set_option maxHeartbeats 0 in
theorem fStep_1 : ∀ i < 7, fStep 1 i (fL 1 i) = fL 1 (i + 1) := by
  intro i hi
  simp only [fStep, sMul_eqK, sInv_eqK, a9K_lin, sAutData, sNfTab_get, sCanon_get, sConj,
    AutData.relOK, ys_fun, AutData.Pk]
  interval_cases i <;> decide +kernel

set_option maxHeartbeats 0 in
theorem fStep_2 : ∀ i < 7, fStep 2 i (fL 2 i) = fL 2 (i + 1) := by
  intro i hi
  simp only [fStep, sMul_eqK, sInv_eqK, a9K_lin, sAutData, sNfTab_get, sCanon_get, sConj,
    AutData.relOK, ys_fun, AutData.Pk]
  interval_cases i <;> decide +kernel

set_option maxHeartbeats 0 in
theorem fStep_3 : ∀ i < 7, fStep 3 i (fL 3 i) = fL 3 (i + 1) := by
  intro i hi
  simp only [fStep, sMul_eqK, sInv_eqK, a9K_lin, sAutData, sNfTab_get, sCanon_get, sConj,
    AutData.relOK, ys_fun, AutData.Pk]
  interval_cases i <;> decide +kernel

end CertificateChecks.KernelO8.SB3872

end
