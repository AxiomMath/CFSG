
module

public import Certificates.Kernel.SporSch.Co2M.ThED
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_join CertificateChecks.KernelSporSch.Co2E

namespace CertificateChecks.KernelSporSch.Co2E

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem perm : allN 26 (fun j => permOK 2300 12 (mask 12) (2300 * 12) (S j) (SI j)) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.Co2E
