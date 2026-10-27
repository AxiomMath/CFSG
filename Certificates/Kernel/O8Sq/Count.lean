module

public import Certificates.Kernel.OmegaEight.E4O8CentData
public import Certificates.Kernel.OmegaEight.Arr3009K
public import Certificates.Data.Kernel.O8Sq
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8Sq

open CFSG.KC.O8Sq CertificateChecks.KernelO8 CertificateChecks.KernelO8.E4C

theorem ch272020k1 : Nat.beq (cntCommK 360 9 (mainK 1) RX) 95 = true := by quickRfl

theorem ch272020k2 : Nat.beq (cntCommK 360 9 (mainK 2) RX) 39 = true := by quickRfl

end CertificateChecks.KernelO8Sq

end
