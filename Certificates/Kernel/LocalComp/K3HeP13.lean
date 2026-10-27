module

public import Certificates.Kernel.LocalComp.K3HeData
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.He

@[expose] noncomputable def fS13 (t : Nat) : Bool := fS (Nat.add 1560 t)

end CertificateChecks.KernelLC.K3.He

#lc_blocks CertificateChecks.KernelLC.K3.He.BS13 CertificateChecks.KernelLC.K3.He.fS13 120 2

namespace CertificateChecks.KernelLC.K3.He

open CFSG.KC.Co3Bfs

theorem cS13 : ∀ t < 120, fS (1560 + t) = true :=
  cover_of_blocks (B := 2) (nb := 60) (by omega) (by decide) BS13.all

end CertificateChecks.KernelLC.K3.He

end
