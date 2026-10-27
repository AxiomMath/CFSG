module

public import Certificates.Data.Kernel.SmithD6.DistK
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

open CFSG.KD.SmithD6

#kc_each CertificateChecks.SmithD6Uw uwdist d6DistOK 0 37

public section

namespace CertificateChecks.SmithD6Uw

#kc_forall_chunks uwDistChunks_ok (fun c => d6DistOK c = true) 37
  CertificateChecks.SmithD6Uw.uwdist 1

end CertificateChecks.SmithD6Uw

end
