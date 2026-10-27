module

public import Certificates.Kernel.SporSch.Ru.B1SCF
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuB1K

@[expose] noncomputable def scr1 (a : Nat) : Bool := scrowF (Nat.add 256 a)

end CertificateChecks.KernelSporSch.RuB1K

#kss_each CertificateChecks.KernelSporSch.RuB1K.SCS1 CertificateChecks.KernelSporSch.RuB1K.scr1 256

end
