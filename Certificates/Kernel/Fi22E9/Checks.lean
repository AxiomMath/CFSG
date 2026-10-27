module

public import Certificates.Kernel.Fi22E9.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22E9

theorem cent3_ok : cent3Chk = true := by quickRfl

theorem centComm_ok : centCommChk = true := by quickRfl

theorem centProd_ok : centProdChk = true := by quickRfl

theorem centQMv_ok : centQMvChk = true := by quickRfl

end CertificateChecks.KernelFi22E9

end
