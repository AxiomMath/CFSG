module

public import Certificates.Kernel.TitsOver.Five.Data
public import Certificates.Kernel.Sporadic.Tits.Words2264
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOver.Five

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelSpor.Tits2264

theorem dp0_eq : Nat.beq (Dp 0) (DKL 0) = true := by quickRfl
theorem dp1_eq : Nat.beq (Dp 1) (DKL 1) = true := by quickRfl
theorem dl0_eq : Nat.beq (pinvS 1755 11 (mask 11) (DKL 0)) (DIL 0) = true := by quickRfl
theorem dl1_eq : Nat.beq (pinvS 1755 11 (mask 11) (DKL 1)) (DIL 1) = true := by quickRfl

theorem dk_eq : Dk = fun k => nIf(Nat.beq k 0, DKL 0, DKL 1) := by
  funext k
  change nIf(Nat.beq k 0, Dp 0, Dp 1) = nIf(Nat.beq k 0, DKL 0, DKL 1)
  rw [Nat.eq_of_beq_eq_true dp0_eq, Nat.eq_of_beq_eq_true dp1_eq]

theorem dik_eq : DIk = fun k => nIf(Nat.beq k 0, DIL 0, DIL 1) := by
  funext k
  unfold DIk
  rw [dk_eq]
  dsimp only
  cases Nat.beq k 0
  · exact Nat.eq_of_beq_eq_true dl1_eq
  · exact Nat.eq_of_beq_eq_true dl0_eq

end CertificateChecks.KernelTitsOver.Five

end
