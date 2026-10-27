module

public import Certificates.Kernel.Fin76bAut.Data
public import Certificates.Data.Kernel.Fin76bAutTab
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFin76bAut

open CFSG.KC.Enum CFSG.KS CFSG.KS.EAut

theorem ch24614E69Tab : e69TabK ET = true := by quickRfl

end CertificateChecks.KernelFin76bAut

end
