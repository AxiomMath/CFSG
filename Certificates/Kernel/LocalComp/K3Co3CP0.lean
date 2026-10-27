module

public import Certificates.Kernel.LocalComp.K3Co3Data
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.Co3

@[expose] noncomputable def fC0 (t : Nat) : Bool := fC (Nat.add 0 t)

end CertificateChecks.KernelLC.K3.Co3

#lc_blocks CertificateChecks.KernelLC.K3.Co3.BC0 CertificateChecks.KernelLC.K3.Co3.fC0 420 7

namespace CertificateChecks.KernelLC.K3.Co3

open CFSG.KC.Co3Bfs

theorem cC0 : ∀ t < 420, fC (0 + t) = true :=
  cover_of_blocks (B := 7) (nb := 60) (by omega) (by decide) BC0.all

end CertificateChecks.KernelLC.K3.Co3

end
