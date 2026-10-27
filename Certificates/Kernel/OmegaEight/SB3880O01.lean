module

public import Certificates.Kernel.OmegaEight.SB3880CK
public import Certificates.Kernel.OmegaEight.SB3873A
public import Certificates.Kernel.OmegaEight.SB3880

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelO8.SB3880

open CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3873

theorem o4b0_1 : ∀ s, 4 ≤ s → s < 8 →
    o4c (MK 0 16 0) vecK 8 (List.range' (8192 * s) 8192) = o4Lit.getD s 0 := by
  intro s hs1 hs2
  interval_cases s <;> decide +kernel

end CertificateChecks.KernelO8.SB3880

end
