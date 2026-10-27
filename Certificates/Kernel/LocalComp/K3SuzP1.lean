module

public import Certificates.Kernel.LocalComp.K3SuzData
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.Suz

@[expose] noncomputable def fS1 (t : Nat) : Bool := fS (Nat.add 660 t)

end CertificateChecks.KernelLC.K3.Suz

#lc_blocks CertificateChecks.KernelLC.K3.Suz.BS1 CertificateChecks.KernelLC.K3.Suz.fS1 660 11

namespace CertificateChecks.KernelLC.K3.Suz

open CFSG.KC.Co3Bfs

theorem cS1 : ∀ t < 660, fS (660 + t) = true :=
  cover_of_blocks (B := 11) (nb := 60) (by omega) (by decide) BS1.all

end CertificateChecks.KernelLC.K3.Suz

end
