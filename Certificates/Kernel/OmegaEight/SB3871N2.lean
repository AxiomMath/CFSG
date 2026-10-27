module

public import Certificates.Kernel.OmegaEight.SB3871NK

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3871

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch

set_option maxHeartbeats 0 in
theorem nStep6 : ∀ s < (nBlocks 6).length, nStepOK 6 s = true := by
  intro s hs
  rw [(by decide +kernel : (nBlocks 6).length = 64)] at hs
  refine nStepOK_of_B (by norm_num) ?_
  interval_cases s <;> decide +kernel

set_option maxHeartbeats 0 in
theorem nStep7 : ∀ s < (nBlocks 7).length, nStepOK 7 s = true := by
  intro s hs
  rw [(by decide +kernel : (nBlocks 7).length = 128)] at hs
  refine nStepOK_of_B (by norm_num) ?_
  interval_cases s <;> decide +kernel

end CertificateChecks.KernelO8.SB3871

end
