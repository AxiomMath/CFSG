module

public import Certificates.Data.Kernel.SmithD6.WtTree
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6

#kc_each CertificateChecks.SmithD6Wt d6wtr d6WtTreeOK 0 37

public section

namespace CertificateChecks.SmithD6Wt

#kc_forall_chunks wtTreeChunks_ok (fun c => d6WtTreeOK c = true) 37
  CertificateChecks.SmithD6Wt.d6wtr 1

end CertificateChecks.SmithD6Wt

end
