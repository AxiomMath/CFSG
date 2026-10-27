module

public import Certificates.Kernel.SporSch.Ru.I2250
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuI

@[expose] noncomputable def allP4 (i : Nat) : Bool := allOKm 4 i

end CertificateChecks.KernelSporSch.RuI

#kss_each CertificateChecks.KernelSporSch.RuI.A4 CertificateChecks.KernelSporSch.RuI.allP4 512

end
