module

public import Certificates.Kernel.Sporadic.Fi22.Sq26560
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.Fi22Sq26560I
  "Certificates/Kernel/Sporadic/Fi22/data/pc26560i.json.gz" 202896 16922551273433244093
  (XI : List Nat)

namespace CertificateChecks.KernelSpor.Fi22Sq26560

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def LI (k : Nat) : Nat := Fi22Sq26560I.XI.getD k 0

theorem permAll : allN 16 (fun k => permOK 3510 12 (mask 12) (3510 * 12) (L k) (LI k)) = true := by
  quickRfl

end CertificateChecks.KernelSpor.Fi22Sq26560

end
