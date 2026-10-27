module

public import Certificates.Data.Kernel.Fi22.LHK
public import Certificates.Kernel.Fi22LH.Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22LH

open CFSG.KS.Fi22LH CFSG.KD.Fi22LH

theorem tall_4 : tallSl R al be bi op ol 4 = true := by quickRfl
theorem tall_5 : tallSl R al be bi op ol 5 = true := by quickRfl
theorem tall_6 : tallSl R al be bi op ol 6 = true := by quickRfl
theorem tall_7 : tallSl R al be bi op ol 7 = true := by quickRfl

end CertificateChecks.KernelFi22LH
