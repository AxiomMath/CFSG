module

public import Certificates.Kernel.E6TwA2.Checks
public import CFSG.Blueprint.ChevalleyRootsInputs

public section

namespace CertificateChecks.KernelE6TwA2

open Certificates.E6TwA2K CFSG.Blueprint.Chevalley

theorem rootsC_eq : rootsC = e6Certificate.roots := by decide +kernel

theorem ch214102_rootsE : rootsOK RP e6Certificate.roots = true := by
  rw [← rootsC_eq]
  exact ch214102_roots

end CertificateChecks.KernelE6TwA2

end
