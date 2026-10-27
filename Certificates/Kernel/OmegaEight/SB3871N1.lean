module

public import Certificates.Kernel.OmegaEight.SB3871N

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3871

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch

set_option maxHeartbeats 0 in
theorem nStep0 : ∀ s < (nBlocks 0).length, nStepOK 0 s = true := by
  intro s hs
  rw [(by decide +kernel : (nBlocks 0).length = 1)] at hs
  interval_cases s
  decide +kernel

set_option maxHeartbeats 0 in
theorem nStep1 : ∀ s < (nBlocks 1).length, nStepOK 1 s = true := by
  intro s hs
  rw [(by decide +kernel : (nBlocks 1).length = 1)] at hs
  interval_cases s
  decide +kernel

set_option maxHeartbeats 0 in
theorem nStep2 : ∀ s < (nBlocks 2).length, nStepOK 2 s = true := by
  intro s hs
  rw [(by decide +kernel : (nBlocks 2).length = 1)] at hs
  interval_cases s
  decide +kernel

set_option maxHeartbeats 0 in
theorem nStep3 : ∀ s < (nBlocks 3).length, nStepOK 3 s = true := by
  intro s hs
  rw [(by decide +kernel : (nBlocks 3).length = 1)] at hs
  interval_cases s
  decide +kernel

set_option maxHeartbeats 0 in
theorem nStep4 : ∀ s < (nBlocks 4).length, nStepOK 4 s = true := by
  intro s hs
  rw [(by decide +kernel : (nBlocks 4).length = 6)] at hs
  interval_cases s <;> decide +kernel

set_option maxHeartbeats 0 in
theorem nStep5 : ∀ s < (nBlocks 5).length, nStepOK 5 s = true := by
  intro s hs
  rw [(by decide +kernel : (nBlocks 5).length = 96)] at hs
  interval_cases s <;> decide +kernel

end CertificateChecks.KernelO8.SB3871

end
