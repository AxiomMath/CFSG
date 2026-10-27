module

public import Certificates.Kernel.LocalComp.K3SuzData
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.Suz

@[expose] noncomputable def fE27 (t : Nat) : Bool := fE (Nat.add 1620 t)

end CertificateChecks.KernelLC.K3.Suz

#lc_blocks CertificateChecks.KernelLC.K3.Suz.BE27 CertificateChecks.KernelLC.K3.Suz.fE27 60 1

namespace CertificateChecks.KernelLC.K3.Suz

open CFSG.KC.Co3Bfs

theorem cE27 : ∀ t < 60, fE (1620 + t) = true :=
  cover_of_blocks (B := 1) (nb := 60) (by omega) (by decide) BE27.all

end CertificateChecks.KernelLC.K3.Suz

end
