module

public import Certificates.Kernel.SporSch.Ru.B1SCF
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuB1K

@[expose] noncomputable def scr5 (a : Nat) : Bool := scrowF (Nat.add 1280 a)

end CertificateChecks.KernelSporSch.RuB1K

#kss_each CertificateChecks.KernelSporSch.RuB1K.SCS5 CertificateChecks.KernelSporSch.RuB1K.scr5 256

end
