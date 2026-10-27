module

public import Certificates.Kernel.Sporadic.OddCore.MN
meta import Certificates.Kernel.Sporadic.OddCore.MN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.MNd

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def r2R : Array (Array Nat) := conjRec pgM pgiM (cM 17)
meta def r2M : Array Nat := cM 17

#kmulh CertificateChecks.KernelSpor.MN.R2 275 9 pgM pgiM r2M 120000
#kfind CertificateChecks.KernelSpor.MN.SYin2 r2R syR
#kfind CertificateChecks.KernelSpor.MN.Uin2 r2R uqM

end CertificateChecks.KernelSpor.MNd

end
