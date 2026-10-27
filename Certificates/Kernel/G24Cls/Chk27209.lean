module

public import Certificates.Kernel.G24Cls.Pack27209
public import Certificates.Kernel.G24Cls.Pack27203
public import Certificates.Kernel.G24Tri.Chain27206
public import Certificates.Kernel.Co1B.Data27207
public import Certificates.Data.Kernel.G24Word
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 100

namespace CertificateChecks.KernelG24.Norm27209

open CFSG.KC.Enum CFSG.KC.G24Key CFSG.KC.G24Word CertificateChecks.KernelG24.Tri27206
  CertificateChecks.KernelG24.Cls27203

theorem kNorm : allN 6 (fun j => normJ (letC (LC.S 0) (LC.SI 0) (LC.S 1) (LC.SI 1))
    (letC (LC.SI 0) (LC.S 0) (LC.SI 1) (LC.S 1)) RG (tw (nat_lit 33) (nat_lit 8589934591) KY)
    (t12 NI) 8 4096 (KernelCo1B.Cent27207.K.SW.getD j []) j) = true := by
  quickRfl

end CertificateChecks.KernelG24.Norm27209

end
