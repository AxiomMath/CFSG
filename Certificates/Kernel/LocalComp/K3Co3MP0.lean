module

public import Certificates.Kernel.LocalComp.K3Co3Data
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.Co3

@[expose] noncomputable def fM0 (t : Nat) : Bool := fM (Nat.add 0 t)

end CertificateChecks.KernelLC.K3.Co3

#lc_blocks CertificateChecks.KernelLC.K3.Co3.BM0 CertificateChecks.KernelLC.K3.Co3.fM0 2160 36

namespace CertificateChecks.KernelLC.K3.Co3

open CFSG.KC.Co3Bfs

theorem cM0 : ∀ t < 2160, fM (0 + t) = true :=
  cover_of_blocks (B := 36) (nb := 60) (by omega) (by decide) BM0.all

end CertificateChecks.KernelLC.K3.Co3

end
