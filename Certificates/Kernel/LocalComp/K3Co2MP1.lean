module

public import Certificates.Kernel.LocalComp.K3Co2Data
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.Co2

@[expose] noncomputable def fM1 (t : Nat) : Bool := fM (Nat.add 240 t)

end CertificateChecks.KernelLC.K3.Co2

#lc_blocks CertificateChecks.KernelLC.K3.Co2.BM1 CertificateChecks.KernelLC.K3.Co2.fM1 240 4

namespace CertificateChecks.KernelLC.K3.Co2

open CFSG.KC.Co3Bfs

theorem cM1 : ∀ t < 240, fM (240 + t) = true :=
  cover_of_blocks (B := 4) (nb := 60) (by omega) (by decide) BM1.all

end CertificateChecks.KernelLC.K3.Co2

end
