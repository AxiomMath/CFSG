module

public import Certificates.Kernel.Sporadic.Suz.Hyp24432Defs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.Spor.CommEnum

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.SuzH2
  "Certificates/Kernel/Sporadic/Suz/data/hyp24432_hyp2.json.gz" 53260 5061307341951441194
  (LS : List Nat) (B : List CFSG.KC.CommBase.BaseRec) (PF : Nat) (ZF : Nat) (DF : Nat)

namespace CertificateChecks.KernelSpor.SuzH2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.CommBase

@[expose] noncomputable def L (k : Nat) : Nat := SuzH.letL LS (SuzTP 2) 3 k

theorem lettersAll : SuzH.letOK L (SuzTP 2) 3 = true := by quickRfl

theorem baseAll : commBaseOK 1782 11 (mask 11) L 7 B PF ZF DF = true := by quickRfl

end CertificateChecks.KernelSpor.SuzH2

end
