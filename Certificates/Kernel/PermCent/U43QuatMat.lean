module

public import Certificates.Data.Kernel.PermCent.U43QuatEls

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelPermCent.U43Quat

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.ComponentClassification.HarrisLit.P1.U43.Quat
  CFSG.LieType.Multipliers.U43 Matrix

theorem quatEls_mat : quatEls.length = quatElDets.length ∧ ∀ x ∈ quatEls.zip quatElDets,
    ((matK x.1.1).map (· ^ 3))ᵀ * matK x.1.1 = 1 ∧ (matK x.1.1).det = uncode x.2 := by
  decide +kernel

end CertificateChecks.KernelPermCent.U43Quat

end
