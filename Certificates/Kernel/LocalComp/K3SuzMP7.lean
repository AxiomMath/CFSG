module

public import Certificates.Kernel.LocalComp.K3SuzData
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.Suz

@[expose] noncomputable def fM7 (t : Nat) : Bool := fM (Nat.add 2100 t)

end CertificateChecks.KernelLC.K3.Suz

#lc_blocks CertificateChecks.KernelLC.K3.Suz.BM7 CertificateChecks.KernelLC.K3.Suz.fM7 87 5

namespace CertificateChecks.KernelLC.K3.Suz

open CFSG.KC.Co3Bfs

theorem cM7 : ∀ t < 87, fM (2100 + t) = true :=
  cover_of_blocks (B := 5) (nb := 18) (by omega) (by decide) BM7.all

end CertificateChecks.KernelLC.K3.Suz

end
