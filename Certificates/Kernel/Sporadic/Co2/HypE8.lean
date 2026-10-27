module

public import Certificates.Kernel.Sporadic.Co2.HypDefs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Co2.ChainA

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.Co2HE
  "Certificates/Kernel/Sporadic/Co2/data/e8.json.gz" 24934 16446239955564470271 (E : List Nat)

namespace CertificateChecks.KernelSpor.Co2HE

theorem e8All : Co2H.e8OK (E.getD 0 0) (E.getD 1 0) (E.getD 2 0) = true := by quickRfl

end CertificateChecks.KernelSpor.Co2HE

end
