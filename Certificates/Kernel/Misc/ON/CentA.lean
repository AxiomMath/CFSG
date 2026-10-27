module

public import CFSG.RankThree.Native.ONTripleCentGenInputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMisc.ON

open CFSG.RankThree.Native.ONTriple

theorem centChk0 : centChkM 0 = true := by quickRfl

end CertificateChecks.KernelMisc.ON

end
