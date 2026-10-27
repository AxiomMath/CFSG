module

public import Certificates.Kernel.Sporadic.ON.Data
public import Certificates.Kernel.Sporadic.ONPw.Data
public import Certificates.Data.Kernel.Spor.ONPwK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONPw

open CFSG.KS.ONPw CertificateChecks.KernelSpor.ON

theorem pw_b0 : wAt TT UU OPW.D (nat_lit 0) = true := by quickRfl

theorem pw_b1 : wAt TT UU OPW.D (nat_lit 227759) = true := by quickRfl

theorem pw_b2 : wAt TT UU OPW.D (nat_lit 100817) = true := by quickRfl

theorem pw_hd : wHd TT UU OPW.D = true := by quickRfl

theorem pw_rho : rhoAll TT UU OPW.D = true := by quickRfl

theorem pw_nr : Nat.beq (OPW.D (nat_lit 70)) (nat_lit 224) = true := by quickRfl

end CertificateChecks.KernelSpor.ONPw

end
