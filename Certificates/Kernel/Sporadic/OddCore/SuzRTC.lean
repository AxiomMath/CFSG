module

public import Certificates.Kernel.Sporadic.OddCore.SuzRTK
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.SuzRTK

theorem cSl0 : cSl 0 = true := by quickRfl
theorem cSl1 : cSl 1 = true := by quickRfl
theorem cSl2 : cSl 2 = true := by quickRfl
theorem cSl3 : cSl 3 = true := by quickRfl
theorem cSl4 : cSl 4 = true := by quickRfl
theorem cSl5 : cSl 5 = true := by quickRfl

end CertificateChecks.KernelSpor.SuzRTK

end
