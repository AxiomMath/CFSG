module

public import Certificates.Data.Kernel.SmithD6.IdCheck
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

open CFSG.KD.SmithD6

#kc_each CertificateChecks.SmithD6Id id7qa id7QaChunkOK 0 37

public section

namespace CertificateChecks.SmithD6Id

#kc_forall_chunks id7QaChunks_ok (fun c => id7QaChunkOK c = true) 37
  CertificateChecks.SmithD6Id.id7qa 1

theorem id7ChkCvK_ok : id7ChkCvK = true := by decide +kernel

theorem id7QaHeadK_ok : id7QaHeadK = true := by decide +kernel

end CertificateChecks.SmithD6Id

end
