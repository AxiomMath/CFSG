module

public import Certificates.Kernel.Fi22Guest.Data
public import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kon_slices CertificateChecks.KernelFi22Guest.wSl 0 120
#kon_join CertificateChecks.KernelFi22Guest.wAll CertificateChecks.KernelFi22Guest.wSl 120

namespace CertificateChecks.KernelFi22Guest

theorem inv_ok : invChk = true := by quickRfl

theorem e_ok : eChk = true := by quickRfl

theorem e3_ok : e3Chk = true := by quickRfl

theorem comm_ok : commChk = true := by quickRfl

theorem prod_ok : prodChk = true := by quickRfl

theorem rel_ok : relChk = true := by quickRfl

theorem qmv_ok : qMvChk = true := by quickRfl

end CertificateChecks.KernelFi22Guest

end
