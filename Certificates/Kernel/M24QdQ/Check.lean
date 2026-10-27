module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDataOmegaDefs

public section

namespace CertificateChecks.KernelM24QdQ

open CFSG.EvenSporadicStandard.M24Std

set_option maxHeartbeats 0 in
theorem qdQData : QdQData := by decide +kernel

end CertificateChecks.KernelM24QdQ
