module

public import Certificates.Kernel.LocalComp.K3Co2Data
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.Co2

@[expose] noncomputable def fS4 (t : Nat) : Bool := fS (Nat.add 1920 t)

end CertificateChecks.KernelLC.K3.Co2

#lc_blocks CertificateChecks.KernelLC.K3.Co2.BS4 CertificateChecks.KernelLC.K3.Co2.fS4 364 8

namespace CertificateChecks.KernelLC.K3.Co2

open CFSG.KC.Co3Bfs

theorem cS4 : ∀ t < 364, fS (1920 + t) = true :=
  cover_of_blocks (B := 8) (nb := 46) (by omega) (by decide) BS4.all

end CertificateChecks.KernelLC.K3.Co2

end
