module

public import Certificates.Kernel.LocalComp.K3Co3Data
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.Co3

@[expose] noncomputable def fC1 (t : Nat) : Bool := fC (Nat.add 420 t)

end CertificateChecks.KernelLC.K3.Co3

#lc_blocks CertificateChecks.KernelLC.K3.Co3.BC1 CertificateChecks.KernelLC.K3.Co3.fC1 25 7

namespace CertificateChecks.KernelLC.K3.Co3

open CFSG.KC.Co3Bfs

theorem cC1 : ∀ t < 25, fC (420 + t) = true :=
  cover_of_blocks (B := 7) (nb := 4) (by omega) (by decide) BC1.all

end CertificateChecks.KernelLC.K3.Co3

end
