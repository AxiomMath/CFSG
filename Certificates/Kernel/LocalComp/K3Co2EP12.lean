module

public import Certificates.Kernel.LocalComp.K3Co2Data
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.Co2

@[expose] noncomputable def fE12 (t : Nat) : Bool := fE (Nat.add 720 t)

end CertificateChecks.KernelLC.K3.Co2

#lc_blocks CertificateChecks.KernelLC.K3.Co2.BE12 CertificateChecks.KernelLC.K3.Co2.fE12 9 1

namespace CertificateChecks.KernelLC.K3.Co2

open CFSG.KC.Co3Bfs

theorem cE12 : ∀ t < 9, fE (720 + t) = true :=
  cover_of_blocks (B := 1) (nb := 9) (by omega) (by decide) BE12.all

end CertificateChecks.KernelLC.K3.Co2

end
