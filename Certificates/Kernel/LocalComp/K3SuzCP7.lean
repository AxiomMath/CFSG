module

public import Certificates.Kernel.LocalComp.K3SuzData
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.Suz

@[expose] noncomputable def fC7 (t : Nat) : Bool := fC (Nat.add 420 t)

end CertificateChecks.KernelLC.K3.Suz

#lc_blocks CertificateChecks.KernelLC.K3.Suz.BC7 CertificateChecks.KernelLC.K3.Suz.fC7 25 1

namespace CertificateChecks.KernelLC.K3.Suz

open CFSG.KC.Co3Bfs

theorem cC7 : ∀ t < 25, fC (420 + t) = true :=
  cover_of_blocks (B := 1) (nb := 25) (by omega) (by decide) BC7.all

end CertificateChecks.KernelLC.K3.Suz

end
