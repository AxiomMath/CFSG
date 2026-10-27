module

public import Certificates.Kernel.LocalComp.ExcU6.FactsD
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.ExcU6

open CFSG.ComponentClassification.RankTwoClassical.ExcU6


theorem facts : censusChainCheck = true ∧ censusCoverCheck = true ∧ censusSizeCheck = true ∧
    censusPointCheck = true ∧ censusDerivCheck = true :=
  ⟨chain_check, cover_check, size_check, point_check, deriv_check⟩

end CertificateChecks.KernelLC.ExcU6

end
