module

public import Certificates.Kernel.LocalComp.K3HeData
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.He

@[expose] noncomputable def fS0 (t : Nat) : Bool := fS (Nat.add 0 t)

end CertificateChecks.KernelLC.K3.He

#lc_blocks CertificateChecks.KernelLC.K3.He.BS0 CertificateChecks.KernelLC.K3.He.fS0 120 2

namespace CertificateChecks.KernelLC.K3.He

open CFSG.KC.Co3Bfs

theorem cS0 : ∀ t < 120, fS (0 + t) = true :=
  cover_of_blocks (B := 2) (nb := 60) (by omega) (by decide) BS0.all

end CertificateChecks.KernelLC.K3.He

end
