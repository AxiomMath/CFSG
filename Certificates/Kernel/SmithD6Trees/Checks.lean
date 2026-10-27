module

public import Certificates.Data.Kernel.SmithD6.Trees
public import Certificates.Data.Kernel.KeyTreeChunks
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

open CFSG.KC.KeyTree CFSG.KD.SmithD6

#kc_each CertificateChecks.SmithD6Trees d6lc (fun c => KT.chunkOK lineTree 2048 365211 J.lineKeysC c)
  0 179

#kc_each CertificateChecks.SmithD6Trees d6wc (fun c => KT.chunkOK wtTree 2048 75735 J.wtC c) 0 37

public section

namespace CertificateChecks.SmithD6Trees

#kc_forall_chunks lineChunks_ok (fun c => KT.chunkOK lineTree 2048 365211 J.lineKeysC c = true)
  179 CertificateChecks.SmithD6Trees.d6lc 1

#kc_forall_chunks wtChunks_ok (fun c => KT.chunkOK wtTree 2048 75735 J.wtC c = true)
  37 CertificateChecks.SmithD6Trees.d6wc 1

theorem lineKeysC_lenC : lenC J.lineKeysC = 179 := by decide +kernel

theorem wtC_lenC : lenC J.wtC = 37 := by decide +kernel

theorem lineTree_size : KT.size lineTree = 365211 := by decide +kernel

theorem wtTree_size : KT.size wtTree = 75735 := by decide +kernel

end CertificateChecks.SmithD6Trees

end
