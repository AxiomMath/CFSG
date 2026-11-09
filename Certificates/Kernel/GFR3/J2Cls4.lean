module

public import Certificates.Kernel.GFR3.J2ClsP
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelGFR3.J2

theorem clsBlock12 : clsBlock (nat_lit 12) = true :=
  (clsBlock_eqP _).trans (by quickRfl)

theorem clsBlock13 : clsBlock (nat_lit 13) = true :=
  (clsBlock_eqP _).trans (by quickRfl)

theorem clsBlock14 : clsBlock (nat_lit 14) = true :=
  (clsBlock_eqP _).trans (by quickRfl)

end CertificateChecks.KernelGFR3.J2

end
