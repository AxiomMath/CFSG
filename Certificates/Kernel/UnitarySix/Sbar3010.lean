
module

public import Certificates.Kernel.UnitarySix.Sbar3010Base

public import Certificates.Kernel.UnitarySix.Fix3010
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelU6

open CFSG.KC.U6 CFSG.EvenSmallLie.UnitarySix CFSG.Sporadic.Schreier

theorem sylow3010 :
    (∀ u ∈ Subgroup.closure {g | g ∈ sGens}, orderOf u = 2 →
        ∃ r ∈ sReps, ∃ c ∈ Subgroup.closure {g | g ∈ sGens}, u = c * r * c⁻¹) ∧
      (∀ r ∈ sReps, orderOf r = 2) ∧
      (∀ p ∈ List.zip sConjs sReps, p.1 * p.2 * p.1⁻¹ ∈ Subgroup.closure {g | g ∈ aGens}) ∧
      (∀ g ∈ sGens, j1 * g = g * j1) ∧
      (∀ x ∈ Subgroup.closure {g | g ∈ sGens}, (∀ g ∈ sGens, x * g = g * x) → x = 1 ∨ x = j1) ∧
      ∀ r ∈ sReps,
        ({p : Fin 693 | r p = p}.ncard = 53 →
          2 ≤ (conjClass (Subgroup.closure {g | g ∈ sGens}) r).ncard) ∧
        ({p : Fin 693 | r p = p}.ncard = 21 →
          8 ≤ (conjClass (Subgroup.closure {g | g ∈ sGens}) r).ncard) :=
  sound3010Y letters_eq aWN_eq kWN_eq tWN_eq sRWN_eq sCWN_eq k3010S (by decide) k3010Y

theorem thompson3010 :
    (∀ x ∈ Subgroup.closure {g | g ∈ tGens}, (∀ g ∈ tGens, x * g = g * x) ∨
        Nat.card {y : Subgroup.closure {g | g ∈ tGens} //
          (y : Equiv.Perm (Fin 693)) * x = x * y} ≤ 16) ∧
      Nat.card {x : Subgroup.closure {g | g ∈ tGens} //
        ∀ g ∈ tGens, (x : Equiv.Perm (Fin 693)) * g = g * x} ≤ 16 ∧
      (∀ x ∈ Subgroup.closure {g | g ∈ tGens}, x ≠ 1 →
        Nat.card {a : Subgroup.closure {g | g ∈ aGens} //
          (a : Equiv.Perm (Fin 693)) * x = x * a} ≤ 32) ∧
      (∀ x ∈ Subgroup.closure {g | g ∈ tGens}, x * x ≠ 1 →
        Nat.card {a : Subgroup.closure {g | g ∈ aGens} //
          (a : Equiv.Perm (Fin 693)) * x = x * a} ≤ 16) ∧
      ∀ b ∈ Subgroup.closure {g | g ∈ tGens}, ∀ c ∈ Subgroup.closure {g | g ∈ tGens},
        b ≠ c → b ≠ 1 → c ≠ 1 → b * b = 1 → c * c = 1 → b * c = c * b →
        Nat.card {a : Subgroup.closure {g | g ∈ aGens} //
          (a : Equiv.Perm (Fin 693)) * b = b * a ∧ (a : Equiv.Perm (Fin 693)) * c = c * a} ≤
          16 :=
  sound3010H letters_eq aWN_eq kWN_eq tWN_eq k3010S (by decide) k3010Y

end CertificateChecks.KernelU6

end
