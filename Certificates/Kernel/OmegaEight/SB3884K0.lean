module

public import Certificates.Kernel.OmegaEight.SB3884
public import Certificates.Kernel.OmegaEight.SB3884KD

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3884

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8.SB3873

set_option maxHeartbeats 0 in
theorem kOK0 : l2KOK 0 kGs0 kL0 = true := by
  have hw : wOK 0 16 = true := by decide +kernel
  have hl : lOK 0 = true := by decide +kernel
  have hio : iotaOK (MK 0 16 0) 0 = true := by decide +kernel
  exact l2KOK_of (k := 0) (m := 16) (z := 0) rfl rfl rfl hw hl hio
    (kDataF_of (by decide) (by decide +kernel) fun s hs => by interval_cases s <;> decide +kernel)

set_option maxHeartbeats 0 in
theorem kOK1 : l2KOK 1 kGs1 kL1 = true := by
  have hw : wOK 0 21 = true := by decide +kernel
  have hl : lOK 0 = true := by decide +kernel
  have hio : iotaOK (MK 0 21 0) 1 = true := by decide +kernel
  exact l2KOK_of (k := 0) (m := 21) (z := 0) rfl rfl rfl hw hl hio
    (kDataF_of (by decide) (by decide +kernel) fun s hs => by interval_cases s <;> decide +kernel)


end CertificateChecks.KernelO8.SB3884

end
