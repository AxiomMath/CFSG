module

public import Certificates.Kernel.SporSch.Ru.B1EF
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuB1K

@[expose] noncomputable def e8r5 (a : Nat) : Bool := e8rowF (Nat.add 1280 a)

end CertificateChecks.KernelSporSch.RuB1K

#kss_each CertificateChecks.KernelSporSch.RuB1K.E8S5 CertificateChecks.KernelSporSch.RuB1K.e8r5 256

end
