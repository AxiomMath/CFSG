module

public import Certificates.Kernel.G24Th799103.InvData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelG24Th

open CFSG.KC.Enum (allN)

theorem ch799103_gem : allN 1365 (fun i => Bool.beq (Nat.testBit EM i)
    (Nat.testBit DM i && !Nat.testBit FM i)) = true := by quickRfl

end CertificateChecks.KernelG24Th

end
