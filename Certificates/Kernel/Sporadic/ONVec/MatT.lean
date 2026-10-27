module

public import Certificates.Kernel.Sporadic.ONVec.Data
public import Certificates.Kernel.Sporadic.ON.Span
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONVec

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CertificateChecks.KernelSpor

theorem symK : tposK (at0 CM) (at0 CM) = true := by quickRfl
theorem symXK : tposK (at0 XI) (at0 XI) = true := by quickRfl
theorem rowsAK : tposK ONV.CA (at0 RA) = true := by quickRfl
theorem rowsBK : tposK ONV.CB (at0 RB) = true := by quickRfl
theorem cuK : tposK (at0 ON.SKL) (at0 CU) = true := by quickRfl
theorem sigK : tposK SR ONS.CA = true := by quickRfl

end CertificateChecks.KernelSpor.ONVec

end
