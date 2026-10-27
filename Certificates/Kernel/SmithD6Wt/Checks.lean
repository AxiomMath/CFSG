module

public import Certificates.Data.Kernel.SmithD6.WtCheck
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6

#kc_each CertificateChecks.SmithD6Wt d6tc (fun c => KT.chunkOK wt64Tree 2048 75735 J.wt64C c) 0 37

#kc_each CertificateChecks.SmithD6Wt d6xc d6ExOK 0 37

#kc_each CertificateChecks.SmithD6Wt d6pc d6PlaneOK 0 37

public section

namespace CertificateChecks.SmithD6Wt

#kc_forall_chunks wt64Chunks_ok (fun c => KT.chunkOK wt64Tree 2048 75735 J.wt64C c = true)
  37 CertificateChecks.SmithD6Wt.d6tc 1

#kc_forall_chunks exChunks_ok (fun c => d6ExOK c = true) 37 CertificateChecks.SmithD6Wt.d6xc 1

#kc_forall_chunks planeChunks_ok (fun c => d6PlaneOK c = true) 37
  CertificateChecks.SmithD6Wt.d6pc 1

theorem wt64C_lenC : lenC J.wt64C = 37 := by decide +kernel

theorem wt64Tree_size : KT.size wt64Tree = 75735 := by decide +kernel

theorem pbC_ppC_length : J.pbC.length = 37 ∧ J.ppC.length = 37 := by decide +kernel

theorem gensT_ok : ∀ g < 13, rhoTOK (gensV.getD g (0, 0)).1 (gensV.getD g (0, 0)).2
    (JT.gensT.getD g []) = true := by decide +kernel

end CertificateChecks.SmithD6Wt

end
