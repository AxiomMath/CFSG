module

public import Certificates.Kernel.FixBoundK.PairData
public import Certificates.Kernel.FixBoundK.PairGData
public import Certificates.Data.Kernel.FixBoundK.PairCp
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelFixBoundK.PairCp

open CFSG.KC.FixBoundK.Pair CertificateChecks.KernelFixBoundK.PairG
  CertificateChecks.KernelFixBoundK.PairD

theorem cpOK : cpAll nB src = true := by quickRfl

end CertificateChecks.KernelFixBoundK.PairCp

end
