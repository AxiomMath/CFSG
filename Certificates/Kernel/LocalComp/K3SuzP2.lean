module

public import Certificates.Kernel.LocalComp.K3SuzData
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.Suz

@[expose] noncomputable def fS2 (t : Nat) : Bool := fS (Nat.add 1320 t)

end CertificateChecks.KernelLC.K3.Suz

#lc_blocks CertificateChecks.KernelLC.K3.Suz.BS2 CertificateChecks.KernelLC.K3.Suz.fS2 660 11

namespace CertificateChecks.KernelLC.K3.Suz

open CFSG.KC.Co3Bfs

theorem cS2 : ∀ t < 660, fS (1320 + t) = true :=
  cover_of_blocks (B := 11) (nb := 60) (by omega) (by decide) BS2.all

end CertificateChecks.KernelLC.K3.Suz

end
