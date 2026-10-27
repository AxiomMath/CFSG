module

public import Certificates.Kernel.LocalComp.K3SuzData
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.Suz

@[expose] noncomputable def fE36 (t : Nat) : Bool := fE (Nat.add 2160 t)

end CertificateChecks.KernelLC.K3.Suz

#lc_blocks CertificateChecks.KernelLC.K3.Suz.BE36 CertificateChecks.KernelLC.K3.Suz.fE36 27 1

namespace CertificateChecks.KernelLC.K3.Suz

open CFSG.KC.Co3Bfs

theorem cE36 : ∀ t < 27, fE (2160 + t) = true :=
  cover_of_blocks (B := 1) (nb := 27) (by omega) (by decide) BE36.all

end CertificateChecks.KernelLC.K3.Suz

end
