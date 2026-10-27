module

public import Certificates.Kernel.Sporadic.ON.Data
public import Certificates.Kernel.Sporadic.ONPw.Data
public import Certificates.Data.Kernel.Spor.ONPwK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONPw

open CFSG.KS.ONPw CertificateChecks.KernelSpor.ON

theorem pw_r7 : recsOK TT UU OPW.D (nat_lit 112) (nat_lit 16) = true := by quickRfl

theorem pw_r8 : recsOK TT UU OPW.D (nat_lit 128) (nat_lit 16) = true := by quickRfl

theorem pw_r9 : recsOK TT UU OPW.D (nat_lit 144) (nat_lit 16) = true := by quickRfl

theorem pw_r10 : recsOK TT UU OPW.D (nat_lit 160) (nat_lit 16) = true := by quickRfl

theorem pw_r11 : recsOK TT UU OPW.D (nat_lit 176) (nat_lit 16) = true := by quickRfl

theorem pw_r12 : recsOK TT UU OPW.D (nat_lit 192) (nat_lit 16) = true := by quickRfl

theorem pw_r13 : recsOK TT UU OPW.D (nat_lit 208) (nat_lit 16) = true := by quickRfl

end CertificateChecks.KernelSpor.ONPw

end
