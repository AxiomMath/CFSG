module

public import Certificates.Kernel.OmegaEight.SB3872W

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3872

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871

set_option maxHeartbeats 0 in
theorem zOK_6 : zOK 6 = true := by
  rw [zOK, List.all_eq_true]
  intro m hm
  rw [show (sLeaves 6).length = 32 from rfl, List.mem_range] at hm
  rw [zAt, zListW_eq]
  simp only [ys_fun, sFixE, sFm, sLeaves, sMul_eqK, a9K_lin, sAutData, sNfTab_get,
    AutData.F, AutData.Pk]
  interval_cases m <;> decide +kernel

set_option maxHeartbeats 0 in
theorem zOK_7 : zOK 7 = true := by
  rw [zOK, List.all_eq_true]
  intro m hm
  rw [show (sLeaves 7).length = 32 from rfl, List.mem_range] at hm
  rw [zAt, zListW_eq]
  simp only [ys_fun, sFixE, sFm, sLeaves, sMul_eqK, a9K_lin, sAutData, sNfTab_get,
    AutData.F, AutData.Pk]
  interval_cases m <;> decide +kernel

end CertificateChecks.KernelO8.SB3872

end
