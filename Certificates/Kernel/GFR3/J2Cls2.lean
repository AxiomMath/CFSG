module

public import Certificates.Kernel.GFR3.J2ClsP
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelGFR3.J2

theorem clsBlock6 : clsBlock (nat_lit 6) = true :=
  (clsBlock_eqP _).trans (by quickRfl)

theorem clsBlock7 : clsBlock (nat_lit 7) = true :=
  (clsBlock_eqP _).trans (by quickRfl)

theorem clsBlock8 : clsBlock (nat_lit 8) = true :=
  (clsBlock_eqP _).trans (by quickRfl)

end CertificateChecks.KernelGFR3.J2

end
