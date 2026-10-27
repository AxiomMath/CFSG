module

public import Certificates.Kernel.Sporadic.RawGenSch
public import Certificates.Kernel.LocalComp.Fi24TwoB.D15027
public meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoBData
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Sporadic.Fi22.C2068
public meta import Certificates.Kernel.Sporadic.Fi22.C3151

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Fi24BR

meta def ddM : Array (Array Nat) :=
  CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime.fi24KddStrong

meta def ddB : Array Nat :=
  CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime.fi24KddBase.toArray

end CertificateChecks.KernelLC.Fi24BR

#ks_rawchain_sl2 CertificateChecks.KernelLC.Fi24BKdd 504 9 16 64 0
  CertificateChecks.KernelLC.Fi24BR.ddM CertificateChecks.KernelLC.Fi24BR.ddB 10
  CertificateChecks.KernelLC.Fi24BW.ddD

end
