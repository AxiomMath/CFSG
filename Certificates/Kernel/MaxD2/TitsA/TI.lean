module

public import Certificates.Kernel.MaxD2.TitsA.Data
public import Certificates.Data.Kernel.MaxD2.Check
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelMaxD2.TitsA

open CFSG.KC.Enum CFSG.KS CFSG.KS.MaxD2 CFSG.KS.PEnum

theorem k_ti : allN 15 (fun i => bIf(Nat.beq (Nat.mod (r32 CN (Nat.succ i)) 5) 0, false, true)) =
    true := by quickRfl

end CertificateChecks.KernelMaxD2.TitsA

end
