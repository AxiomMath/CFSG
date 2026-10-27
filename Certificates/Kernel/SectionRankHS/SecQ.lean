module

public import Certificates.Kernel.SectionRankHS.Seeds
public import Certificates.Data.Kernel.OpsF2KQ
public import Certificates.Data.CFSGNative.Filter.HSData

public section

namespace CertificateChecks.KernelSRHS

open CFSG.KC.OpsF2K CFSG.SectionRank.Native

theorem sec_Q : secQ 20 SA.M SB.M hsSec = true := by decide +kernel

theorem sec_negQ : (!secQ 20 SA.M SB.M { hsSec with outs := [15, 15, 21, 25, 28] }) = true := by
  decide +kernel

theorem sec_neg_seedsQ : (!secQ 20 SB.M SA.M hsSec) = true := by decide +kernel

theorem sec_neg_tQ : (!secQ 20 SA.M SB.M { hsSec with tReg := 21 }) = true := by decide +kernel

end CertificateChecks.KernelSRHS
