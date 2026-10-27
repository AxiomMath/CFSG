module

public import Certificates.Data.Kernel.SmithD6.RankCheck
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6

#kc_each CertificateChecks.SmithD6Kc d6rk d6RankOK 0 6

public section

namespace CertificateChecks.SmithD6Kc

#kc_forall_chunks rank_ok (fun r => d6RankOK r = true) 6 CertificateChecks.SmithD6Kc.d6rk 1

end CertificateChecks.SmithD6Kc

end
