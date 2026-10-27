module

public import Certificates.Kernel.M23Three.Chain

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelM23Three

open CFSG.Certificates.Kernel.PkEnum CFSG.Certificates.Kernel.PkCV

theorem kQF : schP QF = true := by decide +kernel

theorem kOrbits : ((List.finRange QF.baseCount).map fun i =>
    (levelV (strongV QF) QF.base i).entries.length) = [23, 22, 21, 20, 16, 3] := by
  decide +kernel

theorem kRel : relC = true := by decide +kernel

theorem kFix : fixC = true := by decide +kernel

end CertificateChecks.KernelM23Three
