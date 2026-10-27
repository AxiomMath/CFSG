module

public import Certificates.Kernel.Census.McLChain
public import Certificates.Data.Kernel.Ivk8TwoN
public import Certificates.Data.GH74.Ivk8McL
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelIvk8McL

open CFSG.KC.Ivk8N Certificates.Ivk8Two.McL CertificateChecks.KernelCensus

@[expose] noncomputable def mclTwoN : Bool :=
  twoOKN 275 9 [McLS.F 0, McLS.F 1] [1] wordU1 wordU2 wordU3 wordX wordY

theorem mclTwoN_ok : mclTwoN = true := by quickRfl

end CertificateChecks.KernelIvk8McL

end
