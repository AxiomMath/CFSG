module

public import Certificates.Kernel.Sporadic.ON.Data
public import Certificates.Kernel.Sporadic.ONPv.Data
public import Certificates.Data.Kernel.Spor.ONPvK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONPv

open CFSG.KS.ONPv CertificateChecks.KernelSpor.ON

theorem c503_b0 : c503At TT UU OPV.D (nat_lit 0) = true := by quickRfl

theorem c503_b1 : c503At TT UU OPV.D (nat_lit 227759) = true := by quickRfl

theorem c503_b2 : c503At TT UU OPV.D (nat_lit 100817) = true := by quickRfl

theorem c503_hd : c503Hd TT UU OPV.D = true := by quickRfl

end CertificateChecks.KernelSpor.ONPv

end
