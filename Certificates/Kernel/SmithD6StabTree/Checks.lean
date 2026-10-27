module

public import Certificates.Data.Kernel.SmithD6.StabTreeK
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

open CFSG.KC.KeyTree CFSG.KD.SmithD6 CFSG.KD.SmithD6ST

#kc_each CertificateChecks.SmithD6StabTree d6st stTreeOK 0 179

public section

namespace CertificateChecks.SmithD6StabTree

#kc_forall_chunks stTreeChunks_ok (fun c => stTreeOK c = true) 179
  CertificateChecks.SmithD6StabTree.d6st 1

theorem stKeysL_eq : stKeysL = CFSG.KD.SmithD6Nc.stabKeys := by decide +kernel

end CertificateChecks.SmithD6StabTree

end
