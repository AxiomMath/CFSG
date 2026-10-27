module

public import Certificates.Data.Kernel.HSIdent

public section

namespace CertificateChecks.KernelHSIdent

open Certificates.Kernel.HSIdent CFSG.Sporadic.Recognition.HSPinned
  CFSG.Sporadic.Recognition.HSPinned.Native

theorem identCheck_ok : identCheckOn isoList stars = true := by decide +kernel

theorem injCheck_ok : injCheckOn isoList = true := by decide +kernel

end CertificateChecks.KernelHSIdent
