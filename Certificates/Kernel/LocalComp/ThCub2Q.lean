module

public import Certificates.Data.Kernel.OpsF2KQ
public import Certificates.Data.KFCub2Th
public import Certificates.Kernel.EvenBN.Th8Bind

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelLC.ThCub2

open CFSG.KC.OpsF2K CFSG.SectionRank.Native CertificateChecks.Th8

theorem cub2_Q : cub2Q 248 SA.M SB.M thFiveData = true := by decide +kernel

end CertificateChecks.KernelLC.ThCub2

end
