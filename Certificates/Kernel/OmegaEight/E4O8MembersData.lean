module

public import Certificates.Data.E4QuatO8
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.StrChars

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

#ks_chars_of CertificateChecks.KernelO8.e4MS
  (CFSG.ClassicalInvolution.Q3.TL4.E4O8Data.memberWordsStr ())

#kc_repo #kc_json_gz CertificateChecks.KernelO8
  "Certificates/Kernel/OmegaEight/data/E4O8Members.json.gz" 197591 16335964188315069006
  (e4MR : List (List Nat × (Nat × Nat)))

end CertificateChecks.KernelO8

end
