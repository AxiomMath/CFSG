module

public import Certificates.Kernel.TitsOver.Three.Data
public import Certificates.Kernel.Sporadic.Tits.Words2264
public import Certificates.Data.Kernel.Spor.PEnum
public import CFSG.Certificates.Kernel.Spor.PK.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOver.Three

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

theorem lab_lf : allN 2048 (fun x => Nat.beq (PEnum.r32 L x) (pg 11 (mask 11) (LF 0) x)) = true := by
  quickRfl

theorem lab_lit :
    PEnum.r32 L = fun x => nIf(Nat.blt x 2048, pg 11 (mask 11) (LF 0) x, PEnum.r32 L x) := by
  funext x
  cases hb : Nat.blt x 2048
  · rfl
  · exact Nat.eq_of_beq_eq_true (PK.allN_iff.1 lab_lf x (Nat.blt_eq.mp hb))

theorem allN_of_guarded {n w m : Nat} {f : Nat → Bool} (hw : 0 < w) (hn : n ≤ m * w)
    (h : ∀ c < m, allN w (fun t => bIf(Nat.blt (Nat.add (Nat.mul c w) t) n,
      f (Nat.add (Nat.mul c w) t), true)) = true) : allN n f = true := by
  refine PK.allN_iff.2 fun i hi => ?_
  have hc : i / w < m := (Nat.div_lt_iff_lt_mul hw).2 (Nat.lt_of_lt_of_le hi hn)
  have hi' := PK.allN_iff.1 (h (i / w) hc) (i % w) (Nat.mod_lt i hw)
  have e : Nat.add (Nat.mul (i / w) w) (i % w) = i := Nat.div_add_mod' i w
  have hb : Nat.blt i n = true := Nat.blt_eq.mpr hi
  rw [e, hb] at hi'
  exact hi'

end CertificateChecks.KernelTitsOver.Three

end
