module

public import Certificates.Kernel.Fin76bAut.Data
public import Certificates.Kernel.Fin76bOm.UData
public import Certificates.Data.Kernel.Fin76bOm.AutE
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelC24608

open CFSG.KS.EAut CertificateChecks.KernelFin76bAut

@[expose] def RH : Nat := 1415736099094202257672211101862437547355316258848

theorem ch24608AutE : eAEK ET 1920 T = true := by quickRfl

theorem ch24608Iso : eAEIsoU RH J2U.P J3U.P = true := by quickRfl

end CertificateChecks.KernelC24608

end
