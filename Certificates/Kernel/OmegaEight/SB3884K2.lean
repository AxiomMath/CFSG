module

public import Certificates.Kernel.OmegaEight.SB3884
public import Certificates.Kernel.OmegaEight.SB3884KD

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3884

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8.SB3873

set_option maxHeartbeats 0 in
theorem kOK4 : l2KOK 4 kGs4 kL4 = true := by
  have hw : wOK 1 16 = true := by decide +kernel
  have hl : lOK 1 = true := by decide +kernel
  have hio : iotaOK (MK 1 16 24) 4 = true := by decide +kernel
  exact l2KOK_of (k := 1) (m := 16) (z := 24) rfl rfl rfl hw hl hio
    (kDataF_of (by decide) (by decide +kernel) fun s hs => by interval_cases s <;> decide +kernel)

set_option maxHeartbeats 0 in
theorem kOK5 : l2KOK 5 kGs5 kL5 = true := by
  have hw : wOK 1 21 = true := by decide +kernel
  have hl : lOK 1 = true := by decide +kernel
  have hio : iotaOK (MK 1 21 24) 5 = true := by decide +kernel
  exact l2KOK_of (k := 1) (m := 21) (z := 24) rfl rfl rfl hw hl hio
    (kDataF_of (by decide) (by decide +kernel) fun s hs => by interval_cases s <;> decide +kernel)


end CertificateChecks.KernelO8.SB3884

end
