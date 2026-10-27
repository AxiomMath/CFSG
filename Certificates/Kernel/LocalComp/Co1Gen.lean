module

public import Certificates.Data.Kernel.OpsF2KCo1Gen
public import Certificates.Data.Co1GenData
public import Certificates.Kernel.LocalComp.Co1Ops

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelLC.Co1Gen

open CFSG.KC.OpsF2K CFSG.SectionRank.Native CertificateChecks.KernelLC.Co1Ops

set_option maxHeartbeats 0 in
theorem gen_K : co1GenK 24 SA.M SB.M CFSG.SectionRank.Native.Co1Gen.dataFive = true := by
  decide +kernel

end CertificateChecks.KernelLC.Co1Gen

end
