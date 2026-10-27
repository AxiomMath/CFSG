module

public import Certificates.Kernel.Sporadic.ON.Data
public import Certificates.Kernel.Sporadic.ON26682.Data
public import Certificates.Data.Kernel.Spor.ON26682K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON26682

open CFSG.KS.ON26682 CertificateChecks.KernelSpor.ON

theorem ch26682_b0 : ch26682At TT UU O26682.D (nat_lit 0) = true := by quickRfl

theorem ch26682_b1 : ch26682At TT UU O26682.D (nat_lit 227759) = true := by quickRfl

theorem ch26682_b2 : ch26682At TT UU O26682.D (nat_lit 100817) = true := by quickRfl

end CertificateChecks.KernelSpor.ON26682

end
