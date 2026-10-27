module

public import Certificates.Data.Kernel.SmithD6.UwBCheck
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

open CFSG.KD.SmithD6

#kc_each CertificateChecks.SmithD6UwB uwbrec ubOK 0 37

public section

namespace CertificateChecks.SmithD6UwB

#kc_forall_chunks ubChunks_ok (fun c => ubOK c = true) 37
  CertificateChecks.SmithD6UwB.uwbrec 1

theorem ubKeysOK_ok : ubKeysOK = true := by decide +kernel

theorem ubHeadK_ok : ubHeadK = true := by decide +kernel

theorem ubCnt_vals : ubCnt 0 = 42968 ∧ ubCnt 1 = 651 ∧ ubCnt 2 = 18228 ∧ ubCnt 3 = 13888 := by
  decide +kernel

theorem bRC_length : JB.bRC.length = 37 := by decide +kernel

end CertificateChecks.SmithD6UwB

end
