module

public import Certificates.Kernel.Fi22Cls.LabEach
public import Certificates.Kernel.Fi22Cls.LabStrs
public import Certificates.Data.Kernel.LyS0.Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Cls

open CFSG.KD.LyS0

theorem ch13620pLab : parseOK lab LOS.chars 19683 = true := by quickRfl

theorem ch13620pWit : parseOK wit WIS.chars 19683 = true := by quickRfl

end CertificateChecks.KernelFi22Cls

end
