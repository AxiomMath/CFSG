module

public import Certificates.Kernel.Sporadic.Suz.Hyp24432Defs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.Spor.CommEnum

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.SuzHE
  "Certificates/Kernel/Sporadic/Suz/data/hyp24432_e8f.json.gz" 41334 17023025165884950124
  (E : List Nat) (W : List Nat) (WI : List Nat)

namespace CertificateChecks.KernelSpor.SuzHE

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem e8All : SuzH.e8OK (E.getD 0 0) (E.getD 1 0) (E.getD 2 0) = true := by quickRfl

theorem foursAll : bAnd(SuzH.foursOK (W.getD 0 0) (WI.getD 0 0) (SuzTP 2),
    SuzH.foursOK (W.getD 1 0) (WI.getD 1 0) (SuzTP 3)) = true := by quickRfl

end CertificateChecks.KernelSpor.SuzHE

end
