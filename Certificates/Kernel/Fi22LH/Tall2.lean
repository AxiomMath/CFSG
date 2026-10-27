module

public import Certificates.Data.Kernel.Fi22.LHK
public import Certificates.Kernel.Fi22LH.Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22LH

open CFSG.KS.Fi22LH CFSG.KD.Fi22LH

theorem tall_8 : tallSl R al be bi op ol 8 = true := by quickRfl
theorem tall_9 : tallSl R al be bi op ol 9 = true := by quickRfl
theorem tall_10 : tallSl R al be bi op ol 10 = true := by quickRfl
theorem tall_11 : tallSl R al be bi op ol 11 = true := by quickRfl

end CertificateChecks.KernelFi22LH
