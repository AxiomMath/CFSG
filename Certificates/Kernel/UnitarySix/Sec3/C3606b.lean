module

public import Certificates.Kernel.UnitarySix.Sec3.K3606Chk
public import Certificates.Kernel.Misc.Coset.ActBlocks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3

theorem kHb : CFSG.KC.MiscCoset.Act.allR 60 60 (fun i => k3606Run i 1) = true := by allR_blocks 1

theorem kZ2SK : z2sRunK = true := by quickRfl

end CertificateChecks.KernelU6.Sec3
