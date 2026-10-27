module

public import Certificates.Data.Kernel.Stroth77.MnsUniqK
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CertificateChecks.KernelMnsU778702
  "Certificates/Kernel/Stroth77/data/mnsu-778702.json.gz" 9997 6692971916099165201
  (KL : Nat) (CW : Nat) (AB : Nat)

public section

namespace CertificateChecks.KernelMnsU778702

@[expose] noncomputable def utabs : CFSG.KC.Stroth77MN.UTabs := ⟨KL, CW, AB⟩

end CertificateChecks.KernelMnsU778702
