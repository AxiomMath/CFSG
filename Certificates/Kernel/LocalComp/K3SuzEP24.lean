module

public import Certificates.Kernel.LocalComp.K3SuzData
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.Suz

@[expose] noncomputable def fE24 (t : Nat) : Bool := fE (Nat.add 1440 t)

end CertificateChecks.KernelLC.K3.Suz

#lc_blocks CertificateChecks.KernelLC.K3.Suz.BE24 CertificateChecks.KernelLC.K3.Suz.fE24 60 1

namespace CertificateChecks.KernelLC.K3.Suz

open CFSG.KC.Co3Bfs

theorem cE24 : ∀ t < 60, fE (1440 + t) = true :=
  cover_of_blocks (B := 1) (nb := 60) (by omega) (by decide) BE24.all

end CertificateChecks.KernelLC.K3.Suz

end
