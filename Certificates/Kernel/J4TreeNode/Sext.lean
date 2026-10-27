module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Kernel.J4Q.Orbits
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KC.J4TreeN

open CFSG.KC.J4Q CFSG.KD.J4Q CertificateChecks.KernelJ4Q

set_option maxRecDepth 400000 in
theorem sx_check : Nat.beq tabs.sx (sxOf (fstsK (ptsK OR.s1))) = true := by quickRfl

end CFSG.KC.J4TreeN
