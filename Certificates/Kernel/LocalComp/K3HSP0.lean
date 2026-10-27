module

public import Certificates.Kernel.LocalComp.K3HSData
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.HS

@[expose] noncomputable def fS0 (t : Nat) : Bool := fS (Nat.add 0 t)

end CertificateChecks.KernelLC.K3.HS

#lc_blocks CertificateChecks.KernelLC.K3.HS.BS0 CertificateChecks.KernelLC.K3.HS.fS0 300 5

namespace CertificateChecks.KernelLC.K3.HS

open CFSG.KC.Co3Bfs

theorem cS0 : ∀ t < 300, fS (0 + t) = true :=
  cover_of_blocks (B := 5) (nb := 60) (by omega) (by decide) BS0.all

end CertificateChecks.KernelLC.K3.HS

end
