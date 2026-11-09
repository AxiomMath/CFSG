module

public import Certificates.Kernel.GFR3.J2ClsP
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelGFR3.J2

theorem clsBlock9 : clsBlock (nat_lit 9) = true :=
  (clsBlock_eqP _).trans (by quickRfl)

theorem clsBlock10 : clsBlock (nat_lit 10) = true :=
  (clsBlock_eqP _).trans (by quickRfl)

theorem clsBlock11 : clsBlock (nat_lit 11) = true :=
  (clsBlock_eqP _).trans (by quickRfl)

end CertificateChecks.KernelGFR3.J2

end
