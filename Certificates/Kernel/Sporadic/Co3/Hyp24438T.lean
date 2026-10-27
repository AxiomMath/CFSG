module

public import Certificates.Kernel.Sporadic.Co3.Hyp24438Defs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Co3.Single

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.Co3HT
  "Certificates/Kernel/Sporadic/Co3/data/hyp24438_t.json.gz" 6950 6138644131927973994
  (LS : List Nat) (B : List CFSG.KC.CommBase.BaseRec) (PF : Nat) (ZF : Nat) (DF : Nat)

namespace CertificateChecks.KernelSpor.Co3HT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.CommBase

@[expose] noncomputable def L (k : Nat) : Nat := Co3H.letL LS Co3Tt 3 k

theorem lettersAll : Co3H.letOK L Co3Tt 3 = true := by quickRfl

theorem baseAll : commBaseOK 276 9 (mask 9) L 7 B PF ZF DF = true := by quickRfl

end CertificateChecks.KernelSpor.Co3HT

end
