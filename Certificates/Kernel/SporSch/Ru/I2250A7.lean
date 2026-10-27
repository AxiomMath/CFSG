module

public import Certificates.Kernel.SporSch.Ru.I2250
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuI

@[expose] noncomputable def allP7 (i : Nat) : Bool := allOKm 7 i

end CertificateChecks.KernelSporSch.RuI

#kss_each CertificateChecks.KernelSporSch.RuI.A7 CertificateChecks.KernelSporSch.RuI.allP7 512

end
