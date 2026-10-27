module

public import Certificates.Data.Kernel.SmithD6.AdjK
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

open CFSG.KC.KeyTree CFSG.KD.SmithD6 CFSG.KD.SmithD6Adj

#kc_each CertificateChecks.SmithD6Adj d6aj (fun c => d6AdjOK c) 0 37

public section

namespace CertificateChecks.SmithD6Adj

#kc_forall_chunks adjChunks_ok (fun c => d6AdjOK c = true) 37 CertificateChecks.SmithD6Adj.d6aj 1

end CertificateChecks.SmithD6Adj

end
