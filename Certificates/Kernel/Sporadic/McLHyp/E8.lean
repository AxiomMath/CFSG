module

public import Certificates.Kernel.Sporadic.McLHyp.Defs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.LocalComp.McLCent

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.McLHE
  "Certificates/Kernel/Sporadic/McLHyp/data/hyp24430_e8f.json.gz" 5249 2585773670227800669
  (E : List Nat) (W : Nat) (WI : Nat) (RI0 : Nat) (RI1 : Nat)

namespace CertificateChecks.KernelSpor.McLHE

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem rootsAll : bAnd(McLH.rootOK (CertificateChecks.KernelLC.McLC.MC.F 4) RI0,
    McLH.rootOK (CertificateChecks.KernelLC.McLC.MC.F 17) RI1) = true := by quickRfl

theorem e8All : McLH.e8OK (E.getD 0 0) (E.getD 1 0) (E.getD 2 0) = true := by quickRfl

theorem foursAll : McLH.foursOK W WI (CertificateChecks.KernelLC.McLC.MC.F 17) = true := by
  quickRfl

end CertificateChecks.KernelSpor.McLHE

end
