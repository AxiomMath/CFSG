module

public import Certificates.Kernel.Sporadic.ONPar.DefsE
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONPar

theorem tinv_ok : tInvOK = true := by quickRfl

theorem bind_ok : bindOK = true := by quickRfl

theorem ogen_ok : oGenOK = true := by quickRfl

theorem ohd_ok : oHdOK = true := by quickRfl

theorem cenum_ok : cEnumOK = true := by quickRfl

end CertificateChecks.KernelSpor.ONPar

#kon_slices CertificateChecks.KernelSpor.ONPar.cgOK 0 8

#kon_slices CertificateChecks.KernelSpor.ONPar.oEnumOK 0 3

end
