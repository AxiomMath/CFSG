module

public import Certificates.Kernel.SporSch.Ru.B1EF
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuB1K

@[expose] noncomputable def e8r7 (a : Nat) : Bool := e8rowF (Nat.add 1792 a)

end CertificateChecks.KernelSporSch.RuB1K

#kss_each CertificateChecks.KernelSporSch.RuB1K.E8S7 CertificateChecks.KernelSporSch.RuB1K.e8r7 256

end
