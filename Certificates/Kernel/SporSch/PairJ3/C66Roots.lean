module

public import Certificates.Kernel.SporSch.PairJ3.C66RootFns
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.PJ3C66

theorem roots : rootsB = true := by quickRfl

end CertificateChecks.KernelSporSch.PJ3C66

end
