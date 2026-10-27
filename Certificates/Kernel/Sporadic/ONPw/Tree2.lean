module

public import Certificates.Kernel.Sporadic.ONPw.Data
public import Certificates.Data.Kernel.Spor.ONPwK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONPw

open CFSG.KS.ONPw

theorem pw_t8 : nodesOK OPW.D (nat_lit 10080) (nat_lit 1260) = true := by quickRfl

theorem pw_t9 : nodesOK OPW.D (nat_lit 11340) (nat_lit 1260) = true := by quickRfl

theorem pw_t10 : nodesOK OPW.D (nat_lit 12600) (nat_lit 1260) = true := by quickRfl

theorem pw_t11 : nodesOK OPW.D (nat_lit 13860) (nat_lit 1260) = true := by quickRfl

end CertificateChecks.KernelSpor.ONPw

end
