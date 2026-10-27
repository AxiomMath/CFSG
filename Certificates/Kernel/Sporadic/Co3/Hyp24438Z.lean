module

public import Certificates.Kernel.Sporadic.Co3.Hyp24438Defs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Co3.Single

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.Co3HZ
  "Certificates/Kernel/Sporadic/Co3/data/hyp24438_z.json.gz" 6854 6465002587621272105
  (LS : List Nat) (B : List CFSG.KC.CommBase.BaseRec) (PF : Nat) (ZF : Nat) (DF : Nat)

namespace CertificateChecks.KernelSpor.Co3HZ

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.CommBase

@[expose] noncomputable def L (k : Nat) : Nat := Co3H.letL LS Co3Z 3 k

theorem lettersAll : Co3H.letOK L Co3Z 3 = true := by quickRfl

theorem baseAll : commBaseOK 276 9 (mask 9) L 7 B PF ZF DF = true := by quickRfl

end CertificateChecks.KernelSpor.Co3HZ

end
