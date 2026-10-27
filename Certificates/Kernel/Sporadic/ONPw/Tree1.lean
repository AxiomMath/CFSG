module

public import Certificates.Kernel.Sporadic.ONPw.Data
public import Certificates.Data.Kernel.Spor.ONPwK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONPw

open CFSG.KS.ONPw

theorem pw_t4 : nodesOK OPW.D (nat_lit 5040) (nat_lit 1260) = true := by quickRfl

theorem pw_t5 : nodesOK OPW.D (nat_lit 6300) (nat_lit 1260) = true := by quickRfl

theorem pw_t6 : nodesOK OPW.D (nat_lit 7560) (nat_lit 1260) = true := by quickRfl

theorem pw_t7 : nodesOK OPW.D (nat_lit 8820) (nat_lit 1260) = true := by quickRfl

end CertificateChecks.KernelSpor.ONPw

end
