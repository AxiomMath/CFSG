module

public import Certificates.Kernel.Sporadic.ONVec.Data
public import Certificates.Kernel.Sporadic.ON.Span
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONVec

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CertificateChecks.KernelSpor

theorem gramK : imgK CU (fun t => mv CM (at0 ON.SKL t)) (at0 GR) = true := by quickRfl

end CertificateChecks.KernelSpor.ONVec

end
