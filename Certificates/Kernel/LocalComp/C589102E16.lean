module

public import Certificates.Kernel.LocalComp.L34SChk
public import Certificates.Kernel.LocalComp.L34SOData
public import Certificates.Kernel.LocalComp.K589E16Data
public import Certificates.Data.Kernel.S1277K589102E16
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC

open CFSG.KC.L34K
open CFSG.KLie.CT (notB)

theorem k589102e1 : e16K 16 K589E1.T K589B1.T K589K1 20160 L34S.T = true := by quickRfl

theorem k589102e2 : e16K 16 K589E2.T K589B2.T K589K2 20160 L34S.T = true := by quickRfl

end CertificateChecks.KernelLC

end
