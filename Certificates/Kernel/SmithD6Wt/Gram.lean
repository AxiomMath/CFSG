module

public import Certificates.Data.Kernel.SmithD6.GramCheck
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6

#kc_each CertificateChecks.SmithD6Wt d6gr d6GramOK 0 37

public section

namespace CertificateChecks.SmithD6Wt

#kc_forall_chunks gramChunks_ok (fun c => d6GramOK c = true) 37 CertificateChecks.SmithD6Wt.d6gr 1

theorem first_facts : (J.wtC.getD 0 []).getD 0 0 = 1 ∧
    (J.pbC.getD 0 []).getD 0 #[] = #[64, 128, 256, 512, 1024, 2048] := by
  decide +kernel

end CertificateChecks.SmithD6Wt

end
