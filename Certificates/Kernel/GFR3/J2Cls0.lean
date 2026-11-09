module

public import Certificates.Kernel.GFR3.J2ClsP
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelGFR3.J2

theorem clsBlock0 : clsBlock (nat_lit 0) = true :=
  (clsBlock_eqP _).trans (by quickRfl)

theorem clsBlock1 : clsBlock (nat_lit 1) = true :=
  (clsBlock_eqP _).trans (by quickRfl)

theorem clsBlock2 : clsBlock (nat_lit 2) = true :=
  (clsBlock_eqP _).trans (by quickRfl)

end CertificateChecks.KernelGFR3.J2

end
