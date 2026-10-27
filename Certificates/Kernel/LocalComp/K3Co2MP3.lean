module

public import Certificates.Kernel.LocalComp.K3Co2Data
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.Co2

@[expose] noncomputable def fM3 (t : Nat) : Bool := fM (Nat.add 720 t)

end CertificateChecks.KernelLC.K3.Co2

#lc_blocks CertificateChecks.KernelLC.K3.Co2.BM3 CertificateChecks.KernelLC.K3.Co2.fM3 9 4

namespace CertificateChecks.KernelLC.K3.Co2

open CFSG.KC.Co3Bfs

theorem cM3 : ∀ t < 9, fM (720 + t) = true :=
  cover_of_blocks (B := 4) (nb := 3) (by omega) (by decide) BM3.all

end CertificateChecks.KernelLC.K3.Co2

end
