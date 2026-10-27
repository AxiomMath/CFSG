module

public import Certificates.Kernel.Sporadic.ONVec.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONVec

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CertificateChecks.KernelSpor

theorem formK : colsK (at0 CM) ONForm.chars = true := by quickRfl

end CertificateChecks.KernelSpor.ONVec

end
