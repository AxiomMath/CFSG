module

public import Certificates.Data.Kernel.Fi22.LHK
public import Certificates.Kernel.Fi22LH.Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22LH

open CFSG.KS.Fi22LH CFSG.KD.Fi22LH

theorem far : farW QA TF ph lb0 (fd mt 0 16383) (fd mt 80 16383) = true := by quickRfl

end CertificateChecks.KernelFi22LH
