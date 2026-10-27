module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcU6Inputs
public import Certificates.Data.Kernel.LocalComp.ExcDerivSq
public meta import Certificates.Kernel.LocalComp.ExcU6.Gen
public meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Eval
public import Certificates.Kernel.Sporadic.RawGen

public section

set_option maxRecDepth 400000

#kc_eval CertificateChecks.KernelLC.ExcU6 D CertificateChecks.KernelLC.ExcU6.stepU6

#ks_chars CertificateChecks.KernelLC.ExcU6.T1
  CFSG.ComponentClassification.RankTwoClassical.ExcU6.d1Data

#ks_chars CertificateChecks.KernelLC.ExcU6.T2
  CFSG.ComponentClassification.RankTwoClassical.ExcU6.d2Data

#ks_chars CertificateChecks.KernelLC.ExcU6.T3
  CFSG.ComponentClassification.RankTwoClassical.ExcU6.d3Data

end
