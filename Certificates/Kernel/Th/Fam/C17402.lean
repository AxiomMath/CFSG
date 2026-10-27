module

public import Certificates.Kernel.Th.Fam.K
public import CFSG.Certificates.Kernel.Th.Thirteen
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Th.Max3.Data

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh.Fam

open CFSG.KC.Th.Thirteen

theorem ok17402 : th13K thK = true := by quickRfl

end CertificateChecks.KernelTh.Fam

end
