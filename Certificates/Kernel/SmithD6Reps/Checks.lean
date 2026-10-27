module

public import Certificates.Data.Kernel.SmithD6.RepsK
public import Certificates.Data.Kernel.SmithD6.StabK
import all Certificates.Data.SmithD6Model

set_option maxRecDepth 100000

public section

namespace CertificateChecks.SmithD6Reps

open CFSG.KC.KeyTree CFSG.KD.SmithD6 CFSG.KD.SmithD6Stab CFSG.KD.SmithD6Reps

theorem reps_ok : repsL (fun v => KT.memB v wtTree) (tvColsP (1, 2))
    (fun c => tvColsP (pairK (repKeys.getD c 0))) = true := by decide +kernel

theorem plane_ok : planeL (tvColsP (1, 2)) (tvColsP (pairK (repKeys.getD 4 0)))
    (J.wtC.flatten.getD 71 0) (J.wtC.flatten.getD 39 0) = true := by decide +kernel

end CertificateChecks.SmithD6Reps

end
