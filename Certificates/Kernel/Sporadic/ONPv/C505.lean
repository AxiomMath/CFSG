module

public import Certificates.Kernel.Sporadic.ON.Data
public import Certificates.Kernel.Sporadic.ONPv.Data
public import Certificates.Data.Kernel.Spor.ONPvK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONPv

open CFSG.KS.ONPv CertificateChecks.KernelSpor.ON

theorem c505_b0 : c505At TT UU OPV.D (nat_lit 0) = true := by quickRfl

theorem c505_b1 : c505At TT UU OPV.D (nat_lit 227759) = true := by quickRfl

theorem c505_b2 : c505At TT UU OPV.D (nat_lit 100817) = true := by quickRfl

theorem c505_hd : c505Hd TT UU OPV.D = true := by quickRfl

end CertificateChecks.KernelSpor.ONPv

end
