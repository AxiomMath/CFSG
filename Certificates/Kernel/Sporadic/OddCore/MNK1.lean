module

public import Certificates.Kernel.Sporadic.OddCore.MN
meta import Certificates.Kernel.Sporadic.OddCore.MN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.MNd

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def k1R : Array (Array Nat) := mulRec k1M
meta def ids2M : Array (Array Nat) := idsM 2
meta def q1aR : Array (Array Nat) := conjRec k1M k1iM q7M
meta def q1bR : Array (Array Nat) := conjRec k1M k1iM q9M
meta def q1cR : Array (Array Nat) := conjRec k1M k1iM q11M
meta def q1dR : Array (Array Nat) := conjRec k1M k1iM q13M
meta def q1eR : Array (Array Nat) := conjRec k1M k1iM q15M

#kmulh CertificateChecks.KernelSpor.MN.K1 275 9 ids2M k1M idM 120000
#kfind CertificateChecks.KernelSpor.MN.K1in1a q1aR k1R
#kfind CertificateChecks.KernelSpor.MN.K1in1b q1bR k1R
#kfind CertificateChecks.KernelSpor.MN.K1in1c q1cR k1R
#kfind CertificateChecks.KernelSpor.MN.K1in1d q1dR k1R
#kfind CertificateChecks.KernelSpor.MN.K1in1e q1eR k1R

end CertificateChecks.KernelSpor.MNd

end
