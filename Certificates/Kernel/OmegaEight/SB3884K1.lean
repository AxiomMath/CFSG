module

public import Certificates.Kernel.OmegaEight.SB3884
public import Certificates.Kernel.OmegaEight.SB3884KD

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3884

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8.SB3873

set_option maxHeartbeats 0 in
theorem kOK2 : l2KOK 2 kGs2 kL2 = true := by
  have hw : wOK 0 26 = true := by decide +kernel
  have hl : lOK 0 = true := by decide +kernel
  have hio : iotaOK (MK 0 26 0) 2 = true := by decide +kernel
  exact l2KOK_of (k := 0) (m := 26) (z := 0) rfl rfl rfl hw hl hio
    (kDataF_of (by decide) (by decide +kernel) fun s hs => by interval_cases s <;> decide +kernel)

set_option maxHeartbeats 0 in
theorem kOK3 : l2KOK 3 kGs3 kL3 = true := by
  have hw : wOK 0 31 = true := by decide +kernel
  have hl : lOK 0 = true := by decide +kernel
  have hio : iotaOK (MK 0 31 0) 3 = true := by decide +kernel
  exact l2KOK_of (k := 0) (m := 31) (z := 0) rfl rfl rfl hw hl hio
    (kDataF_of (by decide) (by decide +kernel) fun s hs => by interval_cases s <;> decide +kernel)


end CertificateChecks.KernelO8.SB3884

end
