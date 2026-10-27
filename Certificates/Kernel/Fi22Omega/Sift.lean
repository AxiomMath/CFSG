module

public import Certificates.Kernel.I242.YData
public import Certificates.Kernel.Sporadic.Fi22.X2069Final
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Omega

open CFSG.KC.Enum CertificateChecks.KernelI242 CertificateChecks.KernelSpor

theorem ySift : allN 8 (fun r => bAnd(Fi22X.cn (Y.S r), Fi22X.siftP (Y.S r))) = true := by
  quickRfl

end CertificateChecks.KernelFi22Omega

end
