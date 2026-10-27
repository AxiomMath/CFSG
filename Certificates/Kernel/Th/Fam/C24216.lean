module

public import Certificates.Kernel.Th.Fam.K
public import Certificates.Kernel.Th.Fam.LocalTE
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.TransvData

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh.Fam

open CFSG.KC.Th.Expr CertificateChecks.KernelTh.Fam.Local

@[expose] def l24216 : List (TE × TE × Bool) :=
  [(.mul (.q 1) .z, .mul (aelT 1) (.q 1), true), (.mul (.q 1) a1T, .mul (aelT 3) (.q 1), true),
    (.mul (.q 1) a2T, .mul (aelT 4) (.q 1), true), (.mul (.q 1) a3T, .mul (aelT 8) (.q 1), true),
    (.mul (.q 1) g1T, .mul (geT 1 1 2 2) (.q 1), true),
    (.mul (.q 1) g2T, .mul (geT 0 1 0 0) (.q 1), true),
    (.mul (.q 1) g3T, .mul (geT 2 0 3 2) (.q 1), true),
    (.mul (.q 1) g4T, .mul (geT 0 3 0 3) (.q 1), true)]

theorem ok24216 : pairsOK thK l24216 = true := by quickRfl

end CertificateChecks.KernelTh.Fam

end
