
module

public import Certificates.Kernel.L34Cov.AlphaClGlue
public import Certificates.Kernel.L34Cov.SigmaGlue

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.KC.L34W CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.Certificates.CosetEnumeration CFSG.Certificates.L34Cov CFSG.CosetTable Subgroup
open CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CertificateChecks.KernelL34W

theorem quad_lt {e : ℕ} (h : e < 3072) :
    (quad e).1 < 64 ∧ (quad e).2.1 < 4 ∧ (quad e).2.2.1 < 4 ∧ (quad e).2.2.2 < 3 := by
  unfold quad
  dsimp only
  omega

theorem t1_bounds {k l : ℕ} (hk : k < 64) (hl : l < 64) :
    (t1Entry k l).1 < 64 ∧ (t1Entry k l).2.1 < 4 ∧ (t1Entry k l).2.2.1 < 4 ∧
      (t1Entry k l).2.2.2 < 3 := by
  rw [t1Of k l hk hl]
  exact quad_lt (bounds_T bounds_k hk hl)

theorem alpha_bounds {i k : ℕ} (hi : i < 36) (hk : k < 66) :
    (alphaEntry i k).1 < 64 ∧ (alphaEntry i k).2.1 < 4 ∧ (alphaEntry i k).2.2.1 < 4 ∧
      (alphaEntry i k).2.2.2 < 3 := by
  rw [alOf i k hi hk]
  exact quad_lt (bounds_A bounds_k hi hk)

theorem facts22219 :
    (∀ k < 64, ∀ l < 64, (t1Entry k l).1 < 64 ∧ (t1Entry k l).2.1 < 4 ∧
      (t1Entry k l).2.2.1 < 4 ∧ (t1Entry k l).2.2.2 < 3 ∧
      cv (tw k) * cv (tw l) = cv (tw (t1Entry k l).1) * cv (zOf (t1Entry k l))) ∧
    (∀ i < 36,
      abPerm (uA i) = repPerm i * aS * (repPerm i)⁻¹ ∧
      abPerm (uB i) = repPerm i * bS * (repPerm i)⁻¹ ∧
      (∀ k < 64, ((alphaEntry i k).1 < 64 ∧ (alphaEntry i k).2.1 < 4 ∧
          (alphaEntry i k).2.2.1 < 4 ∧ (alphaEntry i k).2.2.2 < 3) ∧
        repPerm i * wordPerm (tg k) * (repPerm i)⁻¹ = wordPerm (tg (alphaEntry i k).1) ∧
        cv (substWord (aut i) (tw k)) = cv (tw (alphaEntry i k).1) * cv (zOf (alphaEntry i k))) ∧
      (∀ j < 2, ((alphaEntry i (64 + j)).1 < 64 ∧ (alphaEntry i (64 + j)).2.1 < 4 ∧
          (alphaEntry i (64 + j)).2.2.1 < 4 ∧ (alphaEntry i (64 + j)).2.2.2 < 3) ∧
        (alphaEntry i (64 + j)).1 = 0 ∧
        cv (substWord (aut i) (zGen j)) = cv (zOf (alphaEntry i (64 + j))))) ∧
    (∀ y ∈ R, (∀ t ∈ T0, y * t * y⁻¹ ∈ T0) →
      ∃ i < 36, ∃ t < 64, y = wordPerm (tg t) * repPerm i) := by
  refine ⟨fun k hk l hl => ⟨(t1_bounds hk hl).1, (t1_bounds hk hl).2.1, (t1_bounds hk hl).2.2.1,
    (t1_bounds hk hl).2.2.2, (t1_spec_k k hk l hl).2⟩, fun i hi => ?_,
    fun y hy hN => exists_decomp_k hy hN⟩
  obtain ⟨hk, hz⟩ := alpha_spec_k hi
  refine ⟨abPerm_uA_k hi, abPerm_uB_k hi, fun k hkl => ⟨alpha_bounds hi (by omega),
    (conj_tg_k hi hkl).2, hk k hkl⟩, fun j hj => ⟨alpha_bounds hi (by omega), (hz j hj).1,
    (hz j hj).2⟩⟩

end CertificateChecks.KernelL34Cov

end
