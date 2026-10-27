module

public import Certificates.Kernel.LocalComp.K3Co3Data
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.Co3

@[expose] noncomputable def fE1 (t : Nat) : Bool := fE (Nat.add 480 t)

end CertificateChecks.KernelLC.K3.Co3

#lc_blocks CertificateChecks.KernelLC.K3.Co3.BE1 CertificateChecks.KernelLC.K3.Co3.fE1 480 8

namespace CertificateChecks.KernelLC.K3.Co3

open CFSG.KC.Co3Bfs

theorem cE1 : ∀ t < 480, fE (480 + t) = true :=
  cover_of_blocks (B := 8) (nb := 60) (by omega) (by decide) BE1.all

end CertificateChecks.KernelLC.K3.Co3

end
