module

public import Certificates.Kernel.HatHe.Tabs
public import Certificates.Kernel.SporSch.HeT.B2114K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHatHe

open CFSG.KC.HatHe
open CertificateChecks.KernelSporSch.HeB14 (C0 C0I C1 C1I)

theorem k7167p0 : with9 C0 (fun G => with9 C0I fun GI =>
    grpK G GI W0 3 512 dW0 dR0 E0 Z0 PA0 SG0 CT0 MB0 CFSG.KD.HatHe.CL0 11) = true := by
  quickRfl

theorem k7167p1 : with9 C1 (fun G => with9 C1I fun GI =>
    grpK G GI W1 4 1024 dW1 dR1 E1 Z1 PA1 SG1 CT1 MB1 CFSG.KD.HatHe.CL1 9) = true := by
  quickRfl

end CertificateChecks.KernelHatHe

end
