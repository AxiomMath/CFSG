module

public import Certificates.Kernel.Sporadic.ON.Span
public import Certificates.Kernel.Sporadic.ONVec.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONVec

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CertificateChecks.KernelSpor

theorem spanK : colsK (at0 ON.RC) ONSpanInv.chars = true := by quickRfl

end CertificateChecks.KernelSpor.ONVec

end
