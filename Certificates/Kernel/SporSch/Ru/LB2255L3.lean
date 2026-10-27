module

public import Certificates.Kernel.SporSch.Ru.LB2255
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Ru.CChain
public import Certificates.Kernel.SporSch.Ru.LChain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuLB

@[expose] noncomputable def cent3 (i : Nat) : Bool := centP 3 i

end CertificateChecks.KernelSporSch.RuLB

#kss_each CertificateChecks.KernelSporSch.RuLB.L3 CertificateChecks.KernelSporSch.RuLB.cent3 4

end
