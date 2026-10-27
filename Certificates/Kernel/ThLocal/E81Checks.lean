module

public import Certificates.Data.Kernel.ThLocal.E81Defs
public import Certificates.Kernel.ThLocal.E81Data
public import Certificates.Kernel.ThCensus.Data
public import Certificates.Kernel.ThCensus.PermData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelThLocal

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.ThCensus CFSG.KC.ThLocal CFSG.KD.ThCensus
  CFSG.KD.ThLocalE81

@[expose] noncomputable def ch9521R (m : Nat) : Bool :=
  e81RepOK (PM 0) (base.getD 0 0) (base.getD 1 0) (base.getD 2 0) reps m (fe.getD m [])

#kc_each ch9521R 0 56

end CertificateChecks.KernelThLocal

end
