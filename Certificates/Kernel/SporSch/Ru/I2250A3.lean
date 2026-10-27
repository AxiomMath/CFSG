module

public import Certificates.Kernel.SporSch.Ru.I2250
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuI

@[expose] noncomputable def allP3 (i : Nat) : Bool := allOKm 3 i

end CertificateChecks.KernelSporSch.RuI

#kss_each CertificateChecks.KernelSporSch.RuI.A3 CertificateChecks.KernelSporSch.RuI.allP3 512

end
