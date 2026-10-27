module

public import Certificates.Kernel.SporSch.Ru.LA2254
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Ru.CChain
public import Certificates.Kernel.SporSch.Ru.LChain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuLA

@[expose] noncomputable def orb1 (i : Nat) : Bool := orbP 1 i

end CertificateChecks.KernelSporSch.RuLA

#kss_each CertificateChecks.KernelSporSch.RuLA.O1 CertificateChecks.KernelSporSch.RuLA.orb1 5

end
