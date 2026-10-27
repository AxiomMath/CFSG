module

public import Certificates.Kernel.Co1B.TriD2045
import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Kernel.SporSch.Co1.GenDag
public meta import Certificates.Kernel.LocalComp.Co1Cen2BIn
public meta import Certificates.Kernel.LocalComp.Co1Cen2BGen
public import CFSG.Assembly.Defs
public meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2BTests
public import Certificates.Kernel.SporSch.Co1.GenDag

public section

#kss_co1dag CertificateChecks.KernelLC.Co1Cen2B.H CertificateChecks.KernelLC.Co1Cen2B.hDag
#kss_co1dag CertificateChecks.KernelLC.Co1Cen2B.C CertificateChecks.KernelLC.Co1Cen2B.cDag

#kc_eval CertificateChecks.KernelLC.Co1Cen2B TA CertificateChecks.KernelLC.Co1Cen2B.triStep
  CertificateChecks.KernelCo1B.Tri2045.TB.PT H.M.L0 H.M.L1 H.M.L2 H.M.L3 H.MI.L2 H.MI.L3 C.M.L8

end
