module

public import CFSG.Certificates.Kernel.E27Orth.SpGlue
public import Certificates.Kernel.E27Orth.Sp8

public section

namespace CertificateChecks.KernelE27Orth.Sp8

open CFSG.KC.Misc.Spec CFSG.KD.E27Orth CFSG.HardMathSupport.Foote.E27 Subgroup Matrix

theorem sp8131003_form : ∀ i < 4 + 4, ∀ j < 4 + 4,
    J.testBit ((4 + 4) * i + j) = decide (i + 4 = j ∨ j + 4 = i) := by
  decide +kernel

theorem sp8131003_fact : ∃ S B : Subgroup (SpJ 4), Nat.card S = 3 ^ 5 ∧ Nat.card B = 3 ^ 4 ∧
    (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧
    (∀ s ∈ S, s ^ 3 = 1 → s ≠ 1 → ∃ x : SpJ 4, x * s * x⁻¹ ∈ B) := by
  obtain ⟨S, B, hS, hB, h⟩ := sp_cover_glue (r := 4) (by norm_num) (by norm_num) sp8131003_form
    sp8131003_sp sp8131003_base sp8131003_tree sp8131003_key sp8131003_left sp8131003_spB
    sp8131003_baseB sp8131003_treeB sp8131003_keyB sp8131003_leftB sp8131003_comm sp8131003_wit
    sp8131003_cover
  exact ⟨S, B, by rw [hS]; norm_num, by rw [hB]; norm_num, h⟩

end CertificateChecks.KernelE27Orth.Sp8

end
