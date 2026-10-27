module

public import Certificates.Data.Kernel.PermCent.U43QuatEls

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelPermCent.U43Quat

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.ComponentClassification.HarrisLit.P1.U43.Quat
  CFSG.LieType.Multipliers.U43 Matrix

theorem quat_mat_c2 :
    ((matK cC2).map (· ^ 3))ᵀ * matK cC2 = 1 ∧ (matK cC2).det = uncode 3 ∧
      matK cC2 * matK cC2inv = 1 ∧ matK cC2 * matK repM1b.1 * matK cC2inv = matK cM1 ∧
      matK (quatEls.getD 1 (0, false)).1 * matK (quatEls.getD 1 (0, false)).1 =
        matK (quatEls.getD 0 (0, false)).1 := by
  decide +kernel

end CertificateChecks.KernelPermCent.U43Quat

end
