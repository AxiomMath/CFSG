module

public import CFSG.Certificates.Kernel.E27Orth.SpGlue
public import Certificates.Kernel.E27Orth.Sp6

public section

namespace CertificateChecks.KernelE27Orth.Sp6

open CFSG.KC.Misc.Spec CFSG.KD.E27Orth CFSG.HardMathSupport.Foote.E27 Subgroup Matrix

theorem sp6131002_form : ∀ i < 3 + 3, ∀ j < 3 + 3,
    J.testBit ((3 + 3) * i + j) = decide (i + 3 = j ∨ j + 3 = i) := by
  decide +kernel

theorem sp6131002_fact : ∃ S : Subgroup (SpJ 3), Nat.card S = 3 ^ 4 ∧
    (∀ c ∈ S, c ≠ 1 → (∀ s ∈ S, s * c = c * s) →
      ∀ v : Fin (3 + 3) → ZMod 2, matJ 3 c *ᵥ v = v → v = 0) ∧
    (∀ a ∈ S, ∀ b ∈ S, a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a → a ≠ 1 → b ∉ zpowers a →
      ∃ i j : ℕ, a ^ i * b ^ j ≠ 1 ∧
        ¬ ∀ v : Fin (3 + 3) → ZMod 2, matJ 3 (a ^ i * b ^ j) *ᵥ v = v → v = 0) := by
  obtain ⟨S, hS, h⟩ := sp_tc_glue (r := 3) (by norm_num) (by norm_num) sp6131002_form
    sp6131002_sp sp6131002_base sp6131002_tree sp6131002_key sp6131002_left sp6131002_cen
    sp6131002_fs sp6131002_pair
  exact ⟨S, by rw [hS]; norm_num, h⟩

end CertificateChecks.KernelE27Orth.Sp6

end
