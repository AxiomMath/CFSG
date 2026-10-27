module

public import Certificates.Kernel.Sporadic.ON.Data
public import Certificates.Kernel.Sporadic.ONPw.Data
public import Certificates.Data.Kernel.Spor.ONPwK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONPw

open CFSG.KS.ONPw CertificateChecks.KernelSpor.ON

theorem pw_r0 : recsOK TT UU OPW.D (nat_lit 0) (nat_lit 16) = true := by quickRfl

theorem pw_r1 : recsOK TT UU OPW.D (nat_lit 16) (nat_lit 16) = true := by quickRfl

theorem pw_r2 : recsOK TT UU OPW.D (nat_lit 32) (nat_lit 16) = true := by quickRfl

theorem pw_r3 : recsOK TT UU OPW.D (nat_lit 48) (nat_lit 16) = true := by quickRfl

theorem pw_r4 : recsOK TT UU OPW.D (nat_lit 64) (nat_lit 16) = true := by quickRfl

theorem pw_r5 : recsOK TT UU OPW.D (nat_lit 80) (nat_lit 16) = true := by quickRfl

theorem pw_r6 : recsOK TT UU OPW.D (nat_lit 96) (nat_lit 16) = true := by quickRfl

end CertificateChecks.KernelSpor.ONPw

end
