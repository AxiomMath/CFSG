module

public import Certificates.Kernel.Sporadic.ONPw.Data
public import Certificates.Data.Kernel.Spor.ONPwPathK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONPw

open CFSG.KC.Enum CFSG.KS.ONPw

theorem pw_paths : allN (nat_lit 224) (pathEq OPW.D) = true := by quickRfl

end CertificateChecks.KernelSpor.ONPw

end
