module

public import Certificates.Kernel.LyModel.Nets
public import Certificates.Data.Kernel.LyModel.Base

public section

namespace CertificateChecks.KernelLyModel

open CFSG.KC CFSG.KC.LyModel CFSG.Sporadic.Recognition.McLMultiplier

theorem ly6110_cover0 : ((mclCover.take 87).all fun r => baseFix (yNets MS r)) = true := by
  decide +kernel

theorem ly6110_cover1 : ((mclCover.drop 87).all fun r => baseFix (yNets MS r)) = true := by
  decide +kernel

end CertificateChecks.KernelLyModel

end
