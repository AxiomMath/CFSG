module

public import Certificates.Data.Kernel.OpsF2KCubQ
public import Certificates.Data.CFSGNative.CTP.StrongP
public import Certificates.Kernel.EvenBN.Th8Bind

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelLC.StrongP14954Th

open CFSG.KC.OpsF2K CFSG.SectionRank.Native CertificateChecks.Th8

theorem th_Q : cubicQ 248 SA.M SB.M thSylow5Data = true := by decide +kernel

theorem th_negQ_t : (!cubicQ 248 SA.M SB.M { thSylow5Data with t := 248 }) = true := by
  decide +kernel

end CertificateChecks.KernelLC.StrongP14954Th

end
