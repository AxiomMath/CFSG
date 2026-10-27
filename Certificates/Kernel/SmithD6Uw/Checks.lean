module

public import Certificates.Data.Kernel.SmithD6.UwCheck
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

open CFSG.KD.SmithD6

#kc_each CertificateChecks.SmithD6Uw uworb uwOrbOK 0 37

public section

namespace CertificateChecks.SmithD6Uw

#kc_forall_chunks uwOrbChunks_ok (fun c => uwOrbOK c = true) 37
  CertificateChecks.SmithD6Uw.uworb 1

theorem uwHeadK_ok : uwHeadK = true := by decide +kernel

theorem uwCnt_vals : uwCnt 0 = 1 ∧ uwCnt 1 = 1302 ∧ uwCnt 2 = 41664 ∧ uwCnt 3 = 32768 := by
  decide +kernel

theorem uwRC_length : JU.uwRC.length = 37 := by decide +kernel

end CertificateChecks.SmithD6Uw

end
