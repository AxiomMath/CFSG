module

public import Certificates.Kernel.LocalComp.ExcU6.Derivs
public import Certificates.Data.Kernel.Griess13.Packed
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.ExcU6

open CFSG.KC.LocalComp.ExcDeriv

theorem kT1 : CFSG.KC.G13.charsEq T1.chars (derivsC (decDerivs D.d1)) = true := by quickRfl
theorem kT2 : CFSG.KC.G13.charsEq T2.chars (derivsC (decDerivs D.d2)) = true := by quickRfl
theorem kT3 : CFSG.KC.G13.charsEq T3.chars (derivsC (decDerivs D.d3)) = true := by quickRfl

end CertificateChecks.KernelLC.ExcU6

end
