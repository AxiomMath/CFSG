module

public import Certificates.Kernel.J3Rank.Data
public import Certificates.Kernel.Q16J3.Data
public import Certificates.Data.Kernel.ElemAbCol
import all Certificates.Data.Kernel.Census.Packed
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelJ3Rank

open CFSG.KC.ElemAbCol CertificateChecks.KernelQ16J3

theorem j3rk_col : colOK 32 5 30 q16J3C.pts.toList j3rkCls = true := by quickRfl

end CertificateChecks.KernelJ3Rank
