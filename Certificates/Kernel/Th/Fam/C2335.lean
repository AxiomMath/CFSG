module

public import Certificates.Kernel.Th.Fam.K
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Th.Max3.Data

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh.Fam

open CFSG.KC.Th.Expr

@[expose] def l2335 : List (TE × TE × Bool) := [(.mul .a .b, .mul .b .a, false)]

theorem ok2335 : pairsOK thK l2335 = true := by quickRfl

end CertificateChecks.KernelTh.Fam

end
