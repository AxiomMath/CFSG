module

public import Certificates.Kernel.L43Q8.Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kc_each CertificateChecks.KernelL43Q8.l43q8Blk 0 8

#kc_each CertificateChecks.KernelL43Q8.l43q8Pr 0 14

namespace CertificateChecks.KernelL43Q8

open CFSG.KD.L43Q8

theorem sqB : ((List.range 512).filter (fun i => eqQ (mulQ (T i) (T i)) T0Q) ==
    (List.range 56).map II) = true := by
  quickRfl

end CertificateChecks.KernelL43Q8

end
