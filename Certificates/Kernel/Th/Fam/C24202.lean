module

public import Certificates.Kernel.Th.Fam.K
public import Certificates.Kernel.Th.Fam.LocalTE
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.TransvData

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh.Fam

open CFSG.KC.Th.Expr CertificateChecks.KernelTh.Fam.Local

@[expose] def l24202 : List (TE × TE × Bool) :=
  [(.mul n1T .z, .mul (aelT 1) n1T, true), (.mul n1T a1T, .mul (aelT 2) n1T, true),
    (.mul n1T a2T, .mul (aelT 10) n1T, true), (.mul n1T a3T, .mul (aelT 15) n1T, true),
    (.mul n2T .z, .mul (aelT 9) n2T, true), (.mul n2T a1T, .mul (aelT 1) n2T, true),
    (.mul n2T a2T, .mul (aelT 5) n2T, true), (.mul n2T a3T, .mul (aelT 2) n2T, true)]

theorem ok24202 : pairsOK thK l24202 = true := by quickRfl

end CertificateChecks.KernelTh.Fam

end
