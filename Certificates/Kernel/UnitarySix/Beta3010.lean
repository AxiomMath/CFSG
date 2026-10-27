
module

public import Certificates.Kernel.UnitarySix.Beta3010Base

public import Certificates.Kernel.UnitarySix.Struct3010
public import Certificates.Kernel.UnitarySix.Polar
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelU6

open CFSG.KC.U6 CFSG.EvenSmallLie.UnitarySix

theorem betaCheck_eq :
    betaCheck = betaCheckG u62Letters kWords beta CFSG.PSL3Four.Native.g₁T
      CFSG.PSL3Four.Native.g₂T CFSG.PSL3Four.Native.g₃T := by
  unfold betaCheck betaCheckG
  rfl

theorem beta3010 : betaCheck = true := by
  rw [betaCheck_eq]
  exact sound3010B letters_eq kWN_eq kBeta kG1 kG2 kG3 (by decide) k3010B

theorem squareBase3010 :
    orderOf o1 = 3 ∧ orderOf o2 = 3 ∧ o1 * j1 = j1 * o1 ∧ o2 * j1 = j1 * o2 ∧
      (o1 * o2) ^ 2 = j1 ∧ y2 ^ 2 = j2 :=
  sound3010Q letters_eq aWN_eq kWN_eq rfl rfl rfl k3010Q

end CertificateChecks.KernelU6

end
