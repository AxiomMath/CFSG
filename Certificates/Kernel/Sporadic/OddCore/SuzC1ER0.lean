module

public import Certificates.Kernel.Sporadic.OddCore.SuzC1ELS
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzC1EL

theorem kRhoI : CFSG.KC.Enum.allN 16 rhoI = true := by quickRfl

theorem kRcIs : CFSG.KC.Enum.allN 16 (fun i => !rcK (c0K i) || rhoIs.contains i) = true := by
  quickRfl

theorem kRhoLight : rhoLight = true := by quickRfl

end CertificateChecks.KernelSpor.SuzC1EL

end
