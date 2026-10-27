module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcLOuterCheckInputs

public section

namespace CertificateChecks.KernelLC.McLY

open CFSG.ComponentClassification.RestrictedStd.Spor

theorem sums : ∀ U : Finset (Fin 10), 0 ∈ U → (∑ l ∈ U, mclYSizes.getD l 0) ∣ 7920 →
    U = {0} ∨ U = Finset.univ := by
  decide +kernel

end CertificateChecks.KernelLC.McLY
