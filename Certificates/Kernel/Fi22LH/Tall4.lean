module

public import Certificates.Data.Kernel.Fi22.LHK
public import Certificates.Kernel.Fi22LH.Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22LH

open CFSG.KS.Fi22LH CFSG.KD.Fi22LH

theorem tall_16 : tallSl R al be bi op ol 16 = true := by quickRfl
theorem tall_17 : tallSl R al be bi op ol 17 = true := by quickRfl
theorem tall_18 : tallSl R al be bi op ol 18 = true := by quickRfl
theorem tall_19 : tallSl R al be bi op ol 19 = true := by quickRfl

end CertificateChecks.KernelFi22LH
