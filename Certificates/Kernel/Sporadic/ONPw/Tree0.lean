module

public import Certificates.Kernel.Sporadic.ONPw.Data
public import Certificates.Data.Kernel.Spor.ONPwK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONPw

open CFSG.KS.ONPw

theorem pw_t0 : nodesOK OPW.D (nat_lit 0) (nat_lit 1260) = true := by quickRfl

theorem pw_t1 : nodesOK OPW.D (nat_lit 1260) (nat_lit 1260) = true := by quickRfl

theorem pw_t2 : nodesOK OPW.D (nat_lit 2520) (nat_lit 1260) = true := by quickRfl

theorem pw_t3 : nodesOK OPW.D (nat_lit 3780) (nat_lit 1260) = true := by quickRfl

end CertificateChecks.KernelSpor.ONPw

end
