module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM22OuterData
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelSchreierFam

open CFSG.Sporadic.Schreier CFSG.Certificates.Kernel.PkEnum

theorem q1_5139K : ((elemsV m22OutCentQ1).any fun u => (elemsV m22OutCentQ1).any fun v =>
    decide (u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧ u * u = 1 ∧ v * v = 1 ∧ u * v = v * u)) = true := by
  decide +kernel

theorem q2_5139K : ((elemsV m22OutCentQ2).any fun u => (elemsV m22OutCentQ2).any fun v =>
    decide (u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧ u * u = 1 ∧ v * v = 1 ∧ u * v = v * u)) = true := by
  decide +kernel

end CertificateChecks.KernelSchreierFam
