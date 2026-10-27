module

public import Certificates.Data.Kernel.SmithD6.EaK
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks
import all Certificates.Data.SmithD6Model

set_option maxRecDepth 100000

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6 CFSG.KD.SmithD6Stab CFSG.KD.SmithD6Ea

#kc_each CertificateChecks.SmithD6Ea d6ea eaChunkOK 0 179

public section

namespace CertificateChecks.SmithD6Ea

#kc_forall_chunks eaChunks_ok (fun c => eaChunkOK c = true) 179 CertificateChecks.SmithD6Ea.d6ea 1

theorem eaKC_length : JEA.eaKC.length = 179 := by decide +kernel

theorem eaKC_flatten_length : JEA.eaKC.flatten.length = 1578 := by decide +kernel

theorem cbw_ok : eaCBWOK = true := by decide +kernel

theorem f4_ok : eaF4OK = true := by decide +kernel

theorem f3_ok : eaF3All = true := by decide +kernel

theorem rig_ok : eaRigP eaInF0K (fun p => pairK (keyAt p)) = true := by decide +kernel

theorem lv0_ok : eaLvOK 0 = true := by decide +kernel

theorem lv1_ok : eaLvOK 1 = true := by decide +kernel

theorem lv2_ok : eaLvOK 2 = true := by decide +kernel

theorem lv3_ok : eaLvOK 3 = true := by decide +kernel

theorem lv4_ok : eaLvOK 4 = true := by decide +kernel

theorem a_ok : eaAOK = true := by decide +kernel

end CertificateChecks.SmithD6Ea

end
