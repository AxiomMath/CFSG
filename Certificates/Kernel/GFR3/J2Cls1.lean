module

public import Certificates.Kernel.GFR3.J2ClsP
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelGFR3.J2

theorem clsBlock3 : clsBlock (nat_lit 3) = true :=
  (clsBlock_eqP _).trans (by quickRfl)

theorem clsBlock4 : clsBlock (nat_lit 4) = true :=
  (clsBlock_eqP _).trans (by quickRfl)

theorem clsBlock5 : clsBlock (nat_lit 5) = true :=
  (clsBlock_eqP _).trans (by quickRfl)

end CertificateChecks.KernelGFR3.J2

end
