module

public import Certificates.Kernel.KGC31M23.Defs
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Quasithin.Vol2.KGFactC31CosetCheck

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M23

theorem kC : Nat.beq D.c 3795 = true := by quickRfl

end CertificateChecks.KernelKGC31M23

#kc_each CertificateChecks.KernelKGC31M23.invBlk 0 4

end
