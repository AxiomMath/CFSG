module

public import Certificates.Data.Kernel.E6TT.Pm
public import Certificates.Kernel.E6TT.WeylData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelE6TT

open CFSG.KC.E6TT Certificates.Data.E6TableT

theorem pmA2 : pmAll (classes (reps.getD 0 [])) W.H0 = true := by quickRfl

end CertificateChecks.KernelE6TT

end
