module

public import Certificates.Kernel.SporSch.Ru.LB2255
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Ru.CChain
public import Certificates.Kernel.SporSch.Ru.LChain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuLB

@[expose] noncomputable def blk1 (i : Nat) : Bool := blkP 1 i

end CertificateChecks.KernelSporSch.RuLB

#kss_each CertificateChecks.KernelSporSch.RuLB.C1 CertificateChecks.KernelSporSch.RuLB.blk1 30

end
