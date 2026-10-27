module

public import Certificates.Kernel.LocalComp.K3HSData
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.HS

@[expose] noncomputable def fS4 (t : Nat) : Bool := fS (Nat.add 1200 t)

end CertificateChecks.KernelLC.K3.HS

#lc_blocks CertificateChecks.KernelLC.K3.HS.BS4 CertificateChecks.KernelLC.K3.HS.fS4 299 5

namespace CertificateChecks.KernelLC.K3.HS

open CFSG.KC.Co3Bfs

theorem cS4 : ∀ t < 299, fS (1200 + t) = true :=
  cover_of_blocks (B := 5) (nb := 60) (by omega) (by decide) BS4.all

end CertificateChecks.KernelLC.K3.HS

end
