
module

public import Certificates.Kernel.SporSch.Co2M.ThEQS0
public import Certificates.Kernel.SporSch.Co2M.ThEQS1
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_join CertificateChecks.KernelSporSch.Co2EQ

namespace CertificateChecks.KernelSporSch.Co2EQ

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem perm : allN 17 (fun j => permOK 1024 11 (mask 11) (1024 * 11) (S j) (SI j)) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.Co2EQ
