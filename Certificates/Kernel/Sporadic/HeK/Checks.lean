module

public import Certificates.Kernel.Sporadic.HeK.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HeK

theorem matOK_ok : matOK = true := by quickRfl
theorem invA_ok : invA = true := by quickRfl
theorem invL_ok : invL = true := by quickRfl
theorem subTree_ok : CFSG.KC.Enum.allN 7 subTree = true := by quickRfl
theorem labOK_ok : labOK = true := by quickRfl
theorem miscOK_ok : miscOK = true := by quickRfl

end CertificateChecks.KernelSpor.HeK

end
