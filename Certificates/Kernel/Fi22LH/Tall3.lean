module

public import Certificates.Data.Kernel.Fi22.LHK
public import Certificates.Kernel.Fi22LH.Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22LH

open CFSG.KS.Fi22LH CFSG.KD.Fi22LH

theorem tall_12 : tallSl R al be bi op ol 12 = true := by quickRfl
theorem tall_13 : tallSl R al be bi op ol 13 = true := by quickRfl
theorem tall_14 : tallSl R al be bi op ol 14 = true := by quickRfl
theorem tall_15 : tallSl R al be bi op ol 15 = true := by quickRfl

end CertificateChecks.KernelFi22LH
