module

public import Certificates.Kernel.LocalComp.K3SuzData
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.Suz

@[expose] noncomputable def fM4 (t : Nat) : Bool := fM (Nat.add 1200 t)

end CertificateChecks.KernelLC.K3.Suz

#lc_blocks CertificateChecks.KernelLC.K3.Suz.BM4 CertificateChecks.KernelLC.K3.Suz.fM4 300 5

namespace CertificateChecks.KernelLC.K3.Suz

open CFSG.KC.Co3Bfs

theorem cM4 : ∀ t < 300, fM (1200 + t) = true :=
  cover_of_blocks (B := 5) (nb := 60) (by omega) (by decide) BM4.all

end CertificateChecks.KernelLC.K3.Suz

end
