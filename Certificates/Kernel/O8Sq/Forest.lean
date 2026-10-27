module

public import Certificates.Kernel.O8Sq.ForestData
public import Certificates.Kernel.OmegaEight.E4O8CentData
public import Certificates.Kernel.OmegaEight.Arr3009K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8Sq

open CFSG.KC.Enum CFSG.KS CFSG.KC.O8Sq CertificateChecks.KernelO8 CertificateChecks.KernelO8.E4C

theorem ch272020r1 : allN 3 (fun j => Nat.beq (RT1.getD j 0)
    (cpathK 360 9 AP.S (mainK 1) (P1.getD j [])) &&
    Nat.beq (pcomp 360 9 (mask 9) (RT1.getD j 0) (mainK 0))
      (pcomp 360 9 (mask 9) (mainK 0) (RT1.getD j 0))) = true := by quickRfl

theorem ch272020r2 : allN 5 (fun j => Nat.beq (RT2.getD j 0)
    (cpathK 360 9 AP.S (mainK 2) (P2.getD j [])) &&
    Nat.beq (pcomp 360 9 (mask 9) (RT2.getD j 0) (mainK 0))
      (pcomp 360 9 (mask 9) (mainK 0) (RT2.getD j 0))) = true := by quickRfl

theorem ch272020f1 : (forestK 360 9 g0K gi0K 6 (fun j => RT1.getD j 0) 3 F1 &&
    Nat.beq F1.length 228) = true := by quickRfl

theorem ch272020f2 : (forestK 360 9 g0K gi0K 6 (fun j => RT2.getD j 0) 5 F2 &&
    Nat.beq F2.length 1404) = true := by quickRfl

end CertificateChecks.KernelO8Sq

end
