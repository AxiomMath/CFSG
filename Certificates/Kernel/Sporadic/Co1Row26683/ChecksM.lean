module

public import Certificates.Kernel.Sporadic.Co1Row26683.DataM
public import Certificates.Kernel.Sporadic.Co1Row26683.DagM
public import Certificates.Kernel.Co1B.Dag2045
public import Certificates.Data.Kernel.Spor.Co1Row26683M
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBCData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co1Row26683

open CFSG.KS.Co1Row26683M CertificateChecks.KernelCo1B.Cent2045 CertificateChecks.KernelSpor
  CFSG.EvenSporadicStandard.Solomon78

theorem ch26683M :
    matK (D2.M (nat_lit 19)) (D2.M (nat_lit 21)) (D1.M (nat_lit 0)) (D1.M (nat_lit 1))
      C26683M.Z.M C26683M.Z.MI C26683M.L.M C26683M.L.MI C26683M.H.M C26683M.H.MI
      co1WordZ co1WordL co1DagH C26683M.W1 C26683M.W2
      (CFSG.KS.Mathieu.nget C26683M.ZV (nat_lit 1)) = true := by
  quickRfl

end CertificateChecks.KernelSpor.Co1Row26683

end
