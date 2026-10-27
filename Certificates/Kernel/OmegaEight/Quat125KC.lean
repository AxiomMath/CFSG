module

public import Certificates.Kernel.OmegaEight.Om0Gen118003K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.Q125

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
open CertificateChecks.KernelO8

theorem kV0Sq125 : Nat.beq (pc om0V om0V) (mainK 0) = true := by quickRfl

theorem neg125V0Sq : Bool.not (Nat.beq (pc om0V (mainK 0)) (mainK 0)) = true := by quickRfl

end CertificateChecks.KernelO8.Q125

end
