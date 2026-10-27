module

public import Certificates.Kernel.U43Cube.Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Cube

open CFSG.KC.Enum CFSG.KS CertificateChecks.KernelU43B CertificateChecks.KernelCU43Aut

theorem kLet : allN 7 (fun j => bAnd(cK (C.S j), inPK (C.S j))) = true := by quickRfl

theorem kBP : allN 3 (fun t => Nat.beq (pg 10 (mask 10) C.BP t) (pg 10 (mask 10) KP t)) = true := by
  quickRfl

end CertificateChecks.KernelU43Cube

end
