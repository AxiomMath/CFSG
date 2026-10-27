module

public import Certificates.Kernel.OmegaEight.SB3872

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3872

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871

set_option maxHeartbeats 0 in
theorem fixmap_check : ((List.range 8).all fun k => (List.range (sLeaves k).length).all fun m =>
    sFixE (sFm k m) || sMapF (sFm k m)) = true := by
  simp only [ys_fun, sMapF, fpArr_get, fpList_eq, sFixE, sFm, sLeaves, sMul_eqK, a9K_lin,
    sAutData, sNfTab_get, AutData.F, AutData.Pk]
  refine all_range_chunks 1 8 fun s hs => ?_
  interval_cases s <;> decide +kernel

end CertificateChecks.KernelO8.SB3872

end
