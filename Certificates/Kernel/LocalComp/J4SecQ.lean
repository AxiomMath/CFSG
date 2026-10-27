module

public import Certificates.Data.Kernel.OpsF2KQ
public import Certificates.Data.CFSGNative.Filter.J4Data
public import Certificates.Kernel.LocalComp.J4Rows

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelLC.J4Sec

open CFSG.KC.OpsF2K CFSG.SectionRank.Native CertificateChecks.KernelLC.J4R

theorem sec_Q : secQ 112 JA.M JB.M j4Sec = true := by decide +kernel

theorem sec_negQ : (!secQ 112 JA.M JB.M { j4Sec with outs := [18, 18, 22, 24, 26] }) = true := by
  decide +kernel

end CertificateChecks.KernelLC.J4Sec

end
