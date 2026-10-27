module

public import Certificates.Kernel.Sporadic.ONPar.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.ON5.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONPar

theorem v_sift : vSift = true := by quickRfl

theorem m_sift : mSift = true := by quickRfl

theorem n_sift : nSift = true := by quickRfl

theorem rel1_ok : rel1 = true := by quickRfl

theorem rel2_ok : rel2 = true := by quickRfl

theorem rel3_ok : rel3 = true := by quickRfl

theorem rel4_ok : rel4 = true := by quickRfl

theorem rel5_ok : rel5 = true := by quickRfl

theorem r_ok : rOK = true := by quickRfl

theorem b_ok : bOK = true := by quickRfl

end CertificateChecks.KernelSpor.ONPar

end
