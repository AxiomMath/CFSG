module

public import Certificates.Kernel.SporSch.Ru.LB2255
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Ru.CChain
public import Certificates.Kernel.SporSch.Ru.LChain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuLB

@[expose] noncomputable def cent2 (i : Nat) : Bool := centP 2 i

end CertificateChecks.KernelSporSch.RuLB

#kss_each CertificateChecks.KernelSporSch.RuLB.L2 CertificateChecks.KernelSporSch.RuLB.cent2 5

end
