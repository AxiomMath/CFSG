module

public import Certificates.Kernel.Sporadic.OddCore.MN
meta import Certificates.Kernel.Sporadic.OddCore.MN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.MNd

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def r1R : Array (Array Nat) := conjRec pgM pgiM (cM 4)
meta def r1M : Array Nat := cM 4

#kmulh CertificateChecks.KernelSpor.MN.R1 275 9 pgM pgiM r1M 120000
#kfind CertificateChecks.KernelSpor.MN.SYin1 r1R syR
#kfind CertificateChecks.KernelSpor.MN.Uin1 r1R uqM

end CertificateChecks.KernelSpor.MNd

end
