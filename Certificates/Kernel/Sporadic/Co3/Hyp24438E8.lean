module

public import Certificates.Kernel.Sporadic.Co3.Hyp24438Defs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Co3.Single

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.Co3HE
  "Certificates/Kernel/Sporadic/Co3/data/hyp24438_e8.json.gz" 2254 13901511896165549233
  (E : List Nat)

namespace CertificateChecks.KernelSpor.Co3HE

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem e8All : Co3H.e8OK (E.getD 0 0) (E.getD 1 0) (E.getD 2 0) = true := by quickRfl

end CertificateChecks.KernelSpor.Co3HE

end
