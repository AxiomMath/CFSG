module

public import Certificates.Data.Kernel.PermCent.U43P1W

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelPermCent.U43P1

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.LieType.Multipliers.U43 Matrix

theorem matDets_ok : ∀ x ∈ matDets,
    ((matK x.1).map (· ^ 3))ᵀ * matK x.1 = 1 ∧ (matK x.1).det = uncode x.2 := by
  decide +kernel

end CertificateChecks.KernelPermCent.U43P1

end
