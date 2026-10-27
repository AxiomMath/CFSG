module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148DGenInputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMisc.ON

open CFSG.RankThree.PartTwo.Sec14.Ronan148D

theorem e27Chk0 : e27ChkM 0 = true := by quickRfl

end CertificateChecks.KernelMisc.ON

end
