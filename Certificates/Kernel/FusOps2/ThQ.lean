module

public import Certificates.Kernel.FusOps2.ThSeeds
public import Certificates.Data.Kernel.OpsF2KFusQ
public import CFSG.RankThree.PartOne.CTP.FusionThInputs

public section

namespace CertificateChecks.KernelFusOps2

open CFSG.KC.OpsF2K CFSG.RankThree.PartOne.CTP.Fus

set_option maxHeartbeats 0 in
theorem thFus_Q : fusQ 248 TA.M TB.M thFusN thFusProg thFus = true := by
  decide +kernel

end CertificateChecks.KernelFusOps2
