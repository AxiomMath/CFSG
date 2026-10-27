module

public import Certificates.Kernel.WeylHyp.Lit
public meta import Certificates.Kernel.Co1B.GenTri2045
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CertificateChecks.KernelWeylHyp.E8h_5

@[expose] def f (s : Nat) : Bool := sliceOK8 (25 + s)

end CertificateChecks.KernelWeylHyp.E8h_5

#kc_slices CertificateChecks.KernelWeylHyp.E8h_5.H CertificateChecks.KernelWeylHyp.E8h_5.f 5

end
