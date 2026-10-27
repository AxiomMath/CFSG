module

public import Certificates.Kernel.OmegaEight.SB3884
public import Certificates.Kernel.OmegaEight.SB3884TH

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3884

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8.SB3873

set_option maxHeartbeats 0 in
theorem th0 : l2THOK 0 thGs0 thPs0 = true :=
  l2THOK_of (by decide +kernel) fun s hs => by interval_cases s <;> decide +kernel

end CertificateChecks.KernelO8.SB3884

end
