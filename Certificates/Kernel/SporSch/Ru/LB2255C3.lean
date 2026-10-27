module

public import Certificates.Kernel.SporSch.Ru.LB2255
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Ru.CChain
public import Certificates.Kernel.SporSch.Ru.LChain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuLB

@[expose] noncomputable def blk3 (i : Nat) : Bool := blkP 3 i

end CertificateChecks.KernelSporSch.RuLB

#kss_each CertificateChecks.KernelSporSch.RuLB.C3 CertificateChecks.KernelSporSch.RuLB.blk3 30

end
