module

public import Certificates.Data.Kernel.O8SqWit
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CertificateChecks.KernelO8Sq

#kc_repo #kc_json_gz CertificateChecks.KernelO8Sq
  "Certificates/Kernel/O8Sq/data/O8SqWit.json.gz" 3318119 15066898396621750152
  (RW : List (List Nat)) (FW : List (Nat × Nat × Nat × Nat)) (HW : List (List Nat))
  (IW : List (Nat × Nat))

end CertificateChecks.KernelO8Sq

end
