module

public import Certificates.Kernel.PermCent.U43QuatP

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelPermCent.U43Quat

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.KC.QuatK

theorem bindsDF : (matK cDi).det ≠ 0 ∧ (matK cI).det ≠ 0 ∧
    (matOK cDi false (QP 15) && matOK cI true (QP 16) &&
      Nat.beq (mulK 820 10 (QP 15) (QP 0)) (mulK 820 10 (QP 0) (QP 15)) &&
      Nat.beq (mulK 820 10 (QP 16) (QP 0)) (mulK 820 10 (QP 0) (QP 16))) = true := by
  decide +kernel

end CertificateChecks.KernelPermCent.U43Quat

end
