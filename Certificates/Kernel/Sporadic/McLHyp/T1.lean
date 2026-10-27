module

public import Certificates.Kernel.Sporadic.McLHyp.Defs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.LocalComp.McLCent

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.McLH1
  "Certificates/Kernel/Sporadic/McLHyp/data/hyp24430_t1.json.gz" 6947 6476725143431574142
  (LS : List Nat) (B : List CFSG.KC.CommBase.BaseRec) (PF : Nat) (ZF : Nat) (DF : Nat)

namespace CertificateChecks.KernelSpor.McLH1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.CommBase

@[expose] noncomputable def L (k : Nat) : Nat :=
  McLH.letL LS (CertificateChecks.KernelLC.McLC.MC.F 17) 3 k

theorem lettersAll : McLH.letOK L (CertificateChecks.KernelLC.McLC.MC.F 17) 3 = true := by
  quickRfl

theorem baseAll : commBaseOK 275 9 (mask 9) L 7 B PF ZF DF = true := by quickRfl

end CertificateChecks.KernelSpor.McLH1

end
