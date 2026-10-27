module

public import Certificates.Data.Kernel.OpsF2KCubQ
public import Certificates.Data.J4SylowThreeIrr
public import Certificates.Kernel.LocalComp.J4Rows

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelLC.J4R

open CFSG.KC.OpsF2K CFSG.SectionRank.Native

theorem j4_3Q : cubicQ 112 JA.M JB.M j4Sylow3Data = true := by decide +kernel

theorem j4_11Q : cubicQ 112 JA.M JB.M j4Sylow11Data = true := by decide +kernel

theorem j4_3irrQ : cubicQ 112 JA.M JB.M j4Sylow3IrrData = true := by decide +kernel

theorem j4_negQ : (!cubicQ 112 JB.M JA.M j4Sylow3Data) = true := by decide +kernel

end CertificateChecks.KernelLC.J4R

end
