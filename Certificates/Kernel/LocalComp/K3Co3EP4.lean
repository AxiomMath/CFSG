module

public import Certificates.Kernel.LocalComp.K3Co3Data
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.K3.Co3

@[expose] noncomputable def fE4 (t : Nat) : Bool := fE (Nat.add 1920 t)

end CertificateChecks.KernelLC.K3.Co3

#lc_blocks CertificateChecks.KernelLC.K3.Co3.BE4 CertificateChecks.KernelLC.K3.Co3.fE4 267 8

namespace CertificateChecks.KernelLC.K3.Co3

open CFSG.KC.Co3Bfs

theorem cE4 : ∀ t < 267, fE (1920 + t) = true :=
  cover_of_blocks (B := 8) (nb := 34) (by omega) (by decide) BE4.all

end CertificateChecks.KernelLC.K3.Co3

end
