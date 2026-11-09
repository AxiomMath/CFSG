module

public import Certificates.Kernel.GFR3.J2ClsP
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelGFR3.J2

theorem clsBlock15 : clsBlock (nat_lit 15) = true :=
  (clsBlock_eqP _).trans (by quickRfl)

theorem clsBlock16 : clsBlock (nat_lit 16) = true :=
  (clsBlock_eqP _).trans (by quickRfl)

theorem clsBlock17 : clsBlock (nat_lit 17) = true :=
  (clsBlock_eqP _).trans (by quickRfl)

end CertificateChecks.KernelGFR3.J2

end
