module

public import Certificates.Data.Kernel.Fi22.LHK
public import Certificates.Kernel.Fi22LH.Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22LH

open CFSG.KS.Fi22LH CFSG.KD.Fi22LH

theorem tall_0 : tallSl R al be bi op ol 0 = true := by quickRfl
theorem tall_1 : tallSl R al be bi op ol 1 = true := by quickRfl
theorem tall_2 : tallSl R al be bi op ol 2 = true := by quickRfl
theorem tall_3 : tallSl R al be bi op ol 3 = true := by quickRfl

end CertificateChecks.KernelFi22LH
