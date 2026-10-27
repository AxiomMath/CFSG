module

public import Certificates.Kernel.LocalComp.K3Co2Data
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.Co2

@[expose] noncomputable def fC2 (t : Nat) : Bool := fC (Nat.add 120 t)

end CertificateChecks.KernelLC.K3.Co2

#lc_blocks CertificateChecks.KernelLC.K3.Co2.BC2 CertificateChecks.KernelLC.K3.Co2.fC2 28 1

namespace CertificateChecks.KernelLC.K3.Co2

open CFSG.KC.Co3Bfs

theorem cC2 : ∀ t < 28, fC (120 + t) = true :=
  cover_of_blocks (B := 1) (nb := 28) (by omega) (by decide) BC2.all

end CertificateChecks.KernelLC.K3.Co2

end
