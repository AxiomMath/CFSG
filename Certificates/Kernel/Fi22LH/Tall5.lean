module

public import Certificates.Data.Kernel.Fi22.LHK
public import Certificates.Kernel.Fi22LH.Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22LH

open CFSG.KS.Fi22LH CFSG.KD.Fi22LH

theorem tall_20 : tallSl R al be bi op ol 20 = true := by quickRfl
theorem tall_21 : tallSl R al be bi op ol 21 = true := by quickRfl
theorem tall_22 : tallSl R al be bi op ol 22 = true := by quickRfl
theorem tall_23 : tallSl R al be bi op ol 23 = true := by quickRfl
theorem tall_24 : tallSl R al be bi op ol 24 = true := by quickRfl
theorem tall_25 : tallSl R al be bi op ol 25 = true := by quickRfl

end CertificateChecks.KernelFi22LH
