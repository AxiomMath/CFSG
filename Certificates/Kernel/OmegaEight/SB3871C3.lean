module

public import Certificates.Kernel.OmegaEight.SB3871C1

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3871

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch

set_option maxHeartbeats 0 in
theorem check3 : sAutCheck3 = true := by
  unfold sAutCheck3
  simp only [sMul_eqK, sInv_eqK, a9K_lin, a9K_co, sAutData, sCanon_get, sConj, AutData.Pk,
    Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine all_range_chunks 1 8 fun s hs => ?_
    interval_cases s <;> decide +kernel
  · decide +kernel
  · refine all_range_chunks 1 8 fun s hs => ?_
    interval_cases s <;> decide +kernel

end CertificateChecks.KernelO8.SB3871

end
