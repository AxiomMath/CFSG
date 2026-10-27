module

public import Certificates.Kernel.LocalComp.L34Para.Data
public import Certificates.Kernel.LocalComp.L34SData
public import Certificates.Kernel.LocalComp.L34RData
public import Certificates.Data.Kernel.L34Field
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Field

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34Field
open CertificateChecks.KernelLC.L34X CertificateChecks.KernelLC.L34Para
open CFSG.KLie.CT (andB notB)

theorem kSyl22209 : syl2K L34R.G L34PT.T L34PT.G L34PB.T L34PR.Y L34PR.YI (RP 1) = true := by
  quickRfl

theorem kField22209 : fieldK L34R.G (RP 1) = true := by quickRfl

end CertificateChecks.KernelLC.L34Field

end
