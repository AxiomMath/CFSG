module

public import Certificates.Kernel.LocalComp.K3SuzData
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.Suz

@[expose] noncomputable def fS3 (t : Nat) : Bool := fS (Nat.add 1980 t)

end CertificateChecks.KernelLC.K3.Suz

#lc_blocks CertificateChecks.KernelLC.K3.Suz.BS3 CertificateChecks.KernelLC.K3.Suz.fS3 121 11

namespace CertificateChecks.KernelLC.K3.Suz

open CFSG.KC.Co3Bfs

theorem cS3 : ∀ t < 121, fS (1980 + t) = true :=
  cover_of_blocks (B := 11) (nb := 11) (by omega) (by decide) BS3.all

end CertificateChecks.KernelLC.K3.Suz

end
