module

public import Certificates.Kernel.SporSch.Ru.LA2254
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Ru.CChain
public import Certificates.Kernel.SporSch.Ru.LChain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuLA

@[expose] noncomputable def orb0 (i : Nat) : Bool := orbP 0 i

end CertificateChecks.KernelSporSch.RuLA

#kss_each CertificateChecks.KernelSporSch.RuLA.O0 CertificateChecks.KernelSporSch.RuLA.orb0 5

end
