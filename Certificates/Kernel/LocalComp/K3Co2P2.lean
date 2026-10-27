module

public import Certificates.Kernel.LocalComp.K3Co2Data
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.Co2

@[expose] noncomputable def fS2 (t : Nat) : Bool := fS (Nat.add 960 t)

end CertificateChecks.KernelLC.K3.Co2

#lc_blocks CertificateChecks.KernelLC.K3.Co2.BS2 CertificateChecks.KernelLC.K3.Co2.fS2 480 8

namespace CertificateChecks.KernelLC.K3.Co2

open CFSG.KC.Co3Bfs

theorem cS2 : ∀ t < 480, fS (960 + t) = true :=
  cover_of_blocks (B := 8) (nb := 60) (by omega) (by decide) BS2.all

end CertificateChecks.KernelLC.K3.Co2

end
