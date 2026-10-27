module

public import Certificates.Kernel.LocalComp.K3Co3Data
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.Co3

@[expose] noncomputable def fM1 (t : Nat) : Bool := fM (Nat.add 2160 t)

end CertificateChecks.KernelLC.K3.Co3

#lc_blocks CertificateChecks.KernelLC.K3.Co3.BM1 CertificateChecks.KernelLC.K3.Co3.fM1 27 36

namespace CertificateChecks.KernelLC.K3.Co3

open CFSG.KC.Co3Bfs

theorem cM1 : ∀ t < 27, fM (2160 + t) = true :=
  cover_of_blocks (B := 36) (nb := 1) (by omega) (by decide) BM1.all

end CertificateChecks.KernelLC.K3.Co3

end
