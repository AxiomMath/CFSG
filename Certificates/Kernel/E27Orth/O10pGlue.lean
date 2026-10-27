module

public import CFSG.Certificates.Kernel.E27Orth.Glue
public import Certificates.Kernel.E27Orth.O10p

public section

namespace CertificateChecks.KernelE27Orth.O10p

open CFSG.KC.Misc.Spec CFSG.KD.E27Orth CFSG.HardMathSupport.Foote.E27 Subgroup Matrix
  CFSG.Assembly.LowTwoRank

theorem o10p131007_form : ∀ a b, pkMat 10 U (ePc 5 a) (ePc 5 b) = umP 5 a b := by decide +kernel

theorem o10p131007_quad (v : Fin 5 ⊕ Fin 5 → ZMod 2) :
    StatedQuadPlus 5 (ZMod 2) v = qf (pkMat 10 U) (v ∘ (ePc 5).symm) :=
  quadPlus_eq (ePc 5) U o10p131007_form v

theorem o10p131007_fact :
    ∃ S₀ B₀ : Subgroup ↥(OrthN (StatedQuadPlus 5 (ZMod 2))), Nat.card S₀ = 243 ∧
      Nat.card B₀ = 81 ∧
      S₀ ≤ (StatedOmega (StatedQuadPlus 5 (ZMod 2))).subgroupOf (OrthN (StatedQuadPlus 5 (ZMod 2))) ∧
      B₀ ≤ (StatedOmega (StatedQuadPlus 5 (ZMod 2))).subgroupOf (OrthN (StatedQuadPlus 5 (ZMod 2))) ∧
      (∀ x ∈ B₀, ∀ y ∈ B₀, x * y = y * x) ∧
      ∀ s ∈ S₀, s ^ 3 = 1 → s ≠ 1 → ∃ x : ↥(OrthN (StatedQuadPlus 5 (ZMod 2))), x * s * x⁻¹ ∈ B₀ :=
  cover_glue (StatedQuadPlus 5 (ZMod 2)) (ePc 5) o10p131007_quad (by norm_num) (by norm_num)
    o10p131007_om o10p131007_base o10p131007_tree o10p131007_key o10p131007_left o10p131007_omB
    o10p131007_baseB o10p131007_treeB o10p131007_keyB o10p131007_leftB o10p131007_comm
    o10p131007_wit o10p131007_cover

end CertificateChecks.KernelE27Orth.O10p

end
