module

public import Certificates.Kernel.OmegaEight.SB3884
public import Certificates.Kernel.OmegaEight.SB3884KD

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3884

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8.SB3873

set_option maxHeartbeats 0 in
theorem kOK6 : l2KOK 6 kGs6 kL6 = true := by
  have hw : wOK 1 26 = true := by decide +kernel
  have hl : lOK 1 = true := by decide +kernel
  have hio : iotaOK (MK 1 26 24) 6 = true := by decide +kernel
  exact l2KOK_of (k := 1) (m := 26) (z := 24) rfl rfl rfl hw hl hio
    (kDataF_of (by decide) (by decide +kernel) fun s hs => by interval_cases s <;> decide +kernel)

set_option maxHeartbeats 0 in
theorem kOK7 : l2KOK 7 kGs7 kL7 = true := by
  have hw : wOK 1 31 = true := by decide +kernel
  have hl : lOK 1 = true := by decide +kernel
  have hio : iotaOK (MK 1 31 24) 7 = true := by decide +kernel
  exact l2KOK_of (k := 1) (m := 31) (z := 24) rfl rfl rfl hw hl hio
    (kDataF_of (by decide) (by decide +kernel) fun s hs => by interval_cases s <;> decide +kernel)


end CertificateChecks.KernelO8.SB3884

end
