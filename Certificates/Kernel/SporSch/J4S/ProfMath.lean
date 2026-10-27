
module

public import CFSG.Sporadic.Schreier.J4SProfile
import Init.Data.Nat.Fold
import Init.Data.Range.Basic
import Init.Data.Array.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J4ProfMath

open CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2

theorem cons_iff : ∀ b < 32, ∀ c < 16, ∀ x : ZMod 2,
    (Fin.cons x (toVecD 4 c) : Fin 5 → ZMod 2) = toVecD 5 b ↔
      x = ((b % 2 : ℕ) : ZMod 2) ∧ c = b / 2 := by
  decide +kernel

theorem surj : ∀ w : Fin 5 → ZMod 2, ∃ b < 32, toVecD 5 b = w := by
  decide +kernel

theorem span : ∀ w : Fin 5 → ZMod 2, ∃ c : Fin 5 → ZMod 2,
    ∑ i, c i • toVecD 5 (![5, 6, 7, 8, 17] i) = w := by
  decide +kernel

theorem indep : ∀ c : Fin 5 → ZMod 2, ∑ i, c i • toVecD 5 (![5, 6, 7, 8, 17] i) = 0 → c = 0 := by
  decide +kernel

theorem ellv : ∀ n < 2048, ell n < 2 ∧ ellV (toVecD 11 n) = (ell n : ZMod 2) := by
  decide +kernel

end CertificateChecks.KernelSporSch.J4ProfMath

end
