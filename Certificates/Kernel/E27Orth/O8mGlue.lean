module

public import CFSG.Certificates.Kernel.E27Orth.Glue
public import Certificates.Kernel.E27Orth.O8m

public section

namespace CertificateChecks.KernelE27Orth.O8m

open CFSG.KC.Misc.Spec CFSG.KD.E27Orth Subgroup Matrix CFSG.Assembly.LowTwoRank

theorem o8m131004_form : ∀ a b, pkMat 8 U (eMc 3 a) (eMc 3 b) = umM 3 a b := by decide +kernel

theorem o8m131004_quad (v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → ZMod 2) :
    StatedQuadMinus 4 (ZMod 2) 1 1 v = qf (pkMat 8 U) (v ∘ (eMc 3).symm) :=
  quadMinus_eq (eMc 3) U o8m131004_form v

theorem o8m131004_fact :
    ∃ S : Subgroup ↥(StatedOmega (StatedQuadMinus 4 (ZMod 2) 1 1)), Nat.card S = 81 ∧
      (∀ c ∈ S, c ≠ 1 → (∀ s ∈ S, s * c = c * s) →
        Nat.card {v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → ZMod 2 //
          ((c : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (ZMod 2)) :
            Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2)
              (ZMod 2)) *ᵥ v = v} = 4) ∧
      (∀ a ∈ S, ∀ b ∈ S, a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a → a ≠ 1 → b ∉ zpowers a →
        ∃ i j : ℕ, a ^ i * b ^ j ≠ 1 ∧ Nat.card {v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → ZMod 2 //
          (((a ^ i * b ^ j : ↥(StatedOmega (StatedQuadMinus 4 (ZMod 2) 1 1))) :
            GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (ZMod 2)) :
            Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2)
              (ZMod 2)) *ᵥ v = v} ≠ 4) :=
  tc_glue (StatedQuadMinus 4 (ZMod 2) 1 1) (eMc 3) o8m131004_quad (by norm_num) (by norm_num)
    o8m131004_om o8m131004_base o8m131004_tree o8m131004_key o8m131004_left o8m131004_cen
    o8m131004_fs o8m131004_pair

end CertificateChecks.KernelE27Orth.O8m

end
