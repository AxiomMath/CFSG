module

public import Certificates.Kernel.SporSch.Ru.LB2255
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Ru.CChain
public import Certificates.Kernel.SporSch.Ru.LChain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuLB

@[expose] noncomputable def blk0 (i : Nat) : Bool := blkP 0 i

end CertificateChecks.KernelSporSch.RuLB

#kss_each CertificateChecks.KernelSporSch.RuLB.C0 CertificateChecks.KernelSporSch.RuLB.blk0 30

end
