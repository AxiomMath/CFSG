module

public import Certificates.Kernel.SporSch.Ru.LA2254
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Ru.CChain
public import Certificates.Kernel.SporSch.Ru.LChain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuLA

@[expose] noncomputable def orb3 (i : Nat) : Bool := orbP 3 i

end CertificateChecks.KernelSporSch.RuLA

#kss_each CertificateChecks.KernelSporSch.RuLA.O3 CertificateChecks.KernelSporSch.RuLA.orb3 4

end
