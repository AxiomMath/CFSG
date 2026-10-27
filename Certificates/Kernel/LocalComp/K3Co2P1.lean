module

public import Certificates.Kernel.LocalComp.K3Co2Data
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.Co2

@[expose] noncomputable def fS1 (t : Nat) : Bool := fS (Nat.add 480 t)

end CertificateChecks.KernelLC.K3.Co2

#lc_blocks CertificateChecks.KernelLC.K3.Co2.BS1 CertificateChecks.KernelLC.K3.Co2.fS1 480 8

namespace CertificateChecks.KernelLC.K3.Co2

open CFSG.KC.Co3Bfs

theorem cS1 : ∀ t < 480, fS (480 + t) = true :=
  cover_of_blocks (B := 8) (nb := 60) (by omega) (by decide) BS1.all

end CertificateChecks.KernelLC.K3.Co2

end
