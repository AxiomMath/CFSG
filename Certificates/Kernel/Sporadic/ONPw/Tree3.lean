module

public import Certificates.Kernel.Sporadic.ONPw.Data
public import Certificates.Data.Kernel.Spor.ONPwK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONPw

open CFSG.KS.ONPw

theorem pw_t12 : nodesOK OPW.D (nat_lit 15120) (nat_lit 1260) = true := by quickRfl

theorem pw_t13 : nodesOK OPW.D (nat_lit 16380) (nat_lit 1260) = true := by quickRfl

theorem pw_t14 : nodesOK OPW.D (nat_lit 17640) (nat_lit 1260) = true := by quickRfl

theorem pw_t15 : nodesOK OPW.D (nat_lit 18900) (nat_lit 1260) = true := by quickRfl

end CertificateChecks.KernelSpor.ONPw

end
