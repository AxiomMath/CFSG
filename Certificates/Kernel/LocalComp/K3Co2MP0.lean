module

public import Certificates.Kernel.LocalComp.K3Co2Data
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.Co2

@[expose] noncomputable def fM0 (t : Nat) : Bool := fM (Nat.add 0 t)

end CertificateChecks.KernelLC.K3.Co2

#lc_blocks CertificateChecks.KernelLC.K3.Co2.BM0 CertificateChecks.KernelLC.K3.Co2.fM0 240 4

namespace CertificateChecks.KernelLC.K3.Co2

open CFSG.KC.Co3Bfs

theorem cM0 : ∀ t < 240, fM (0 + t) = true :=
  cover_of_blocks (B := 4) (nb := 60) (by omega) (by decide) BM0.all

end CertificateChecks.KernelLC.K3.Co2

end
