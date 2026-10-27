module

public import Certificates.Data.Kernel.SmithD6.KcCheck
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6

#kc_each CertificateChecks.SmithD6Kc d6km d6KcMeetOK 0 37

public section

namespace CertificateChecks.SmithD6Kc

#kc_forall_chunks meetChunks_ok (fun c => d6KcMeetOK c = true) 37 CertificateChecks.SmithD6Kc.d6km 1

theorem thrAll_ok : kcThrAll = 135 := by decide +kernel

theorem span_ok : d6SpanOK = true := by decide +kernel

end CertificateChecks.SmithD6Kc

end
