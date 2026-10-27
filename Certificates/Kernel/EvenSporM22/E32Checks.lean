module

public import Certificates.Data.Kernel.EvenSporM22.E32Defs

public section

namespace CertificateChecks.KernelEvenSporM22

open CFSG.KC.EvenSporM22

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e32K_true : CheckPropK ∧ xPropK := by
  decide +kernel

theorem checkPropK_true : CheckPropK := e32K_true.1

theorem xPropK_true : xPropK := e32K_true.2

end CertificateChecks.KernelEvenSporM22
