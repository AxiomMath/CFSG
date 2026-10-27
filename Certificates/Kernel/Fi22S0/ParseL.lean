module

public import Certificates.Kernel.Fi22S0.ParseChk
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22S0

open CFSG.KD.LyS0

theorem ch131101pL : parseOK LRec LS.chars 59049 = true := by quickRfl

end CertificateChecks.KernelFi22S0

end
