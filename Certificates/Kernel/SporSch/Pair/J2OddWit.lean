module

public import Certificates.Kernel.SporSch.Pair.J2Chain
public import Certificates.Data.Kernel.SporSch.J2OddWit
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelSporSch.J2OW260410
  "Certificates/Kernel/SporSch/Pair/data/j2odd260410.json.gz" 138081 4739855335608371106
  (ws : List (List Nat)) (ps : List Nat) (powL : List (Nat × Nat × Nat))
  (conjL : List (Nat × Nat × Nat)) (commL : List (Nat × Nat)) (ordL : List (Nat × Nat))
  (s3L : List Nat) (s5L : List Nat) (s5VL : List Nat) (k4L : List Nat) (repL : List Nat)
  (auxL : List Nat)

namespace CertificateChecks.KernelSporSch.J2OW260410

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.MOC CFSG.KS.SporSch.J2OW

@[expose] def nT : Nat := 146

theorem j2owTab : tabK 315 9 (mask 9) (pidn 315 9) (PJ2.S 0) (PJ2.S 1)
    (powK 315 9 (mask 9) (pidn 315 9) (PJ2.S 0) 1) (powK 315 9 (mask 9) (pidn 315 9) (PJ2.S 1) 2)
    nT ws ps = true := by quickRfl

theorem j2owPow : powsK 315 9 (mask 9) (pidn 315 9) nT ps powL = true := by quickRfl

theorem j2owConj : conjsK 315 9 (mask 9) nT ps conjL = true := by quickRfl

theorem j2owComm : commsK 315 9 (mask 9) nT ps commL = true := by quickRfl

theorem j2owOrd : ordsK 315 9 (mask 9) (pidn 315 9) nT ps ordL = true := by quickRfl

theorem j2owS3 : closedK 315 9 (mask 9) nT ps s3L s3L = true := by quickRfl

theorem j2owS5 : closedK 315 9 (mask 9) nT ps s5L s5L = true := by quickRfl

theorem j2owS5V : closedK 315 9 (mask 9) nT ps s5VL s5VL = true := by quickRfl

theorem j2owK4 : closedK 315 9 (mask 9) nT ps k4L k4L = true := by quickRfl

end CertificateChecks.KernelSporSch.J2OW260410

end
