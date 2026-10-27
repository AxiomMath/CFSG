module

public import CFSG.Certificates.Kernel.E27Orth.Glue
public import Certificates.Kernel.E27Orth.O8p

public section

namespace CertificateChecks.KernelE27Orth.O8p

open CFSG.KC.Misc.Spec CFSG.KD.E27Orth CFSG.HardMathSupport.Foote.E27 Subgroup Matrix
  CFSG.Assembly.LowTwoRank

theorem o8p131006_form : ∀ a b, pkMat 8 U (ePc 4 a) (ePc 4 b) = umP 4 a b := by decide +kernel

theorem o8p131006_quad (v : Fin 4 ⊕ Fin 4 → ZMod 2) :
    StatedQuadPlus 4 (ZMod 2) v = qf (pkMat 8 U) (v ∘ (ePc 4).symm) :=
  quadPlus_eq (ePc 4) U o8p131006_form v

theorem o8p131006_fact :
    ∃ S₀ B₀ : Subgroup ↥(OrthN (StatedQuadPlus 4 (ZMod 2))), Nat.card S₀ = 243 ∧
      Nat.card B₀ = 81 ∧
      S₀ ≤ (StatedOmega (StatedQuadPlus 4 (ZMod 2))).subgroupOf (OrthN (StatedQuadPlus 4 (ZMod 2))) ∧
      B₀ ≤ (StatedOmega (StatedQuadPlus 4 (ZMod 2))).subgroupOf (OrthN (StatedQuadPlus 4 (ZMod 2))) ∧
      (∀ x ∈ B₀, ∀ y ∈ B₀, x * y = y * x) ∧
      ∀ s ∈ S₀, s ^ 3 = 1 → s ≠ 1 → ∃ x : ↥(OrthN (StatedQuadPlus 4 (ZMod 2))), x * s * x⁻¹ ∈ B₀ :=
  cover_glue (StatedQuadPlus 4 (ZMod 2)) (ePc 4) o8p131006_quad (by norm_num) (by norm_num)
    o8p131006_om o8p131006_base o8p131006_tree o8p131006_key o8p131006_left o8p131006_omB
    o8p131006_baseB o8p131006_treeB o8p131006_keyB o8p131006_leftB o8p131006_comm o8p131006_wit
    o8p131006_cover

end CertificateChecks.KernelE27Orth.O8p

end
