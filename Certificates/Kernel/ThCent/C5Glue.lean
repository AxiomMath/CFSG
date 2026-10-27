module

public import Certificates.Kernel.ThCent.LGlue
public import Certificates.Kernel.ThCent.C5C0
public import Certificates.Kernel.ThCent.C5C1
public import Certificates.Kernel.ThCent.C5C2
public import Certificates.Kernel.ThCent.C5C3
public import CFSG.Certificates.Kernel.ThCent.Cent5Sound
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.CubeFacts
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiTransp
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools

public section

namespace CertificateChecks.KernelThList

open CFSG.Sporadic.Th CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.Th.Spec.FwdRel
  CFSG.KC.ThCent CFSG.KD.ThCent.L CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThList
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFiveNative CFSG.KD CFSG.KD.ThCent

set_option maxRecDepth 100000

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

#kc_forall_tree cn5_all (fun k => CFSG.KD.ThCent.L.cn5 k = true) 60 CFSG.KD.ThCent.L.cn5_


theorem mat_c5 : 𝕄 c5 = pkMat C5 := by
  obtain ⟨-, -, -, hk⟩ := KernelThCent.fwd_mats
  have hx := mat_R5 94 (by decide)
  have hy := mat_R5 105 (by decide)
  unfold c5 C5
  rw [mat_mul, mat_mul, mat_mul, mat_pow, mat_pow, hx, hy, pkMat_mulB hk, pkMat_mulB hk,
    pkMat_mulB hk, pkMat_powB hk _ _ 3 (by norm_num), pkMat_powB hk _ _ 3 (by norm_num)]

theorem el5_mat (i : ℕ) (hi : i < L5.E.length) :
    𝕄 (el5 i) = pkMat (wordR ThS.c ThS.rm ThS.ONE V5 (L5.E[i]).1) := by
  have hw := words_of_map E5_words i hi
  unfold el5
  rw [← hw]
  exact mat_word mat_R5 (regsOK_spec E5_regs i hi).1

theorem cube_mem_Q (i j k : ℕ) :
    slpJ a b prog5 94 ^ i * slpJ a b prog5 105 ^ j * c5 ^ k ∈
      Subgroup.closure ({slpJ a b prog5 94, slpJ a b prog5 105} : Set ↥J) := by
  have hxQ : slpJ a b prog5 94 ∈
      Subgroup.closure ({slpJ a b prog5 94, slpJ a b prog5 105} : Set ↥J) :=
    Subgroup.subset_closure (by simp)
  have hyQ : slpJ a b prog5 105 ∈
      Subgroup.closure ({slpJ a b prog5 94, slpJ a b prog5 105} : Set ↥J) :=
    Subgroup.subset_closure (by simp)
  have hcQ : c5 ∈ Subgroup.closure ({slpJ a b prog5 94, slpJ a b prog5 105} : Set ↥J) := by
    unfold c5
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxQ hyQ)
      (Subgroup.pow_mem _ hxQ _)) (Subgroup.pow_mem _ hyQ _)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ hxQ _)
    (Subgroup.pow_mem _ hyQ _)) (Subgroup.pow_mem _ hcQ _)

theorem letter_conj {t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} (ht : t ∈ lett5) :
    ∀ q ∈ Subgroup.closure ({slpJ a b prog5 94, slpJ a b prog5 105} : Set ↥J),
      slpJ a b prog5 t.1 * q * (slpJ a b prog5 t.1)⁻¹ ∈
        Subgroup.closure ({slpJ a b prog5 94, slpJ a b prog5 105} : Set ↥J) := by
  obtain ⟨-, -, -, hk⟩ := KernelThCent.fwd_mats
  have hx := mat_R5 94 (by decide)
  have hy := mat_R5 105 (by decide)
  have hb : t.1 ∈ regs5 ∧ t.2.1 ∈ regs5 ∧ t.2.2.1 < 8 ∧ t.2.2.2.1 < 8 ∧ t.2.2.2.2.1 < 8 ∧
      t.2.2.2.2.2.1 < 8 ∧ t.2.2.2.2.2.2.1 < 8 ∧ t.2.2.2.2.2.2.2 < 8 := by
    simp only [lett5, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> decide
  obtain ⟨h1, h2, hi, hj, hk1, hi', hj', hk2⟩ := hb
  have h := List.all_eq_true.1 lett5_ok t ht
  unfold let5 at h
  rw [strictF_eq] at h
  obtain ⟨e1, e2, e3⟩ := letterOK_sound hk hi hj hk1 hi' hj' hk2 h
  have hr := mat_R5 _ h1
  have hr' := mat_R5 _ h2
  have hinv : (slpJ a b prog5 t.1)⁻¹ = slpJ a b prog5 t.2.1 :=
    inv_eq_of_mul_eq_one_right (mat_inj (by rw [mat_mul, hr, hr', e1, mat_one]))
  have m1 : slpJ a b prog5 t.1 * slpJ a b prog5 94 * (slpJ a b prog5 t.1)⁻¹ =
      slpJ a b prog5 94 ^ t.2.2.1 * slpJ a b prog5 105 ^ t.2.2.2.1 * c5 ^ t.2.2.2.2.1 :=
    mat_inj (by
      rw [hinv, mat_mul, mat_mul, hr, hx, hr', e2, mat_mul, mat_mul, mat_pow, mat_pow, mat_pow, hx,
        hy, mat_c5])
  have m2 : slpJ a b prog5 t.1 * slpJ a b prog5 105 * (slpJ a b prog5 t.1)⁻¹ =
      slpJ a b prog5 94 ^ t.2.2.2.2.2.1 * slpJ a b prog5 105 ^ t.2.2.2.2.2.2.1 *
        c5 ^ t.2.2.2.2.2.2.2 :=
    mat_inj (by
      rw [hinv, mat_mul, mat_mul, hr, hy, hr', e3, mat_mul, mat_mul, mat_pow, mat_pow, mat_pow, hx,
        hy, mat_c5])
  exact CFSG.HardMathSupport.Dickson.I271.conj_mem_closure_pair
    (by rw [m1]; exact cube_mem_Q _ _ _) (by rw [m2]; exact cube_mem_Q _ _ _)

theorem th_cent5 :
    (∀ i < 3000, ∀ q ∈ Subgroup.closure ({slpJ a b prog5 94, slpJ a b prog5 105} : Set ↥J),
      el5 i * q * (el5 i)⁻¹ ∈
        Subgroup.closure ({slpJ a b prog5 94, slpJ a b prog5 105} : Set ↥J)) ∧
      ∀ i < 3000, el5 i * slpJ a b prog5 94 = slpJ a b prog5 94 * el5 i →
        el5 i * slpJ a b prog5 105 = slpJ a b prog5 105 * el5 i → ∃ k < 5, el5 i = c5 ^ k := by
  obtain ⟨-, -, -, hk⟩ := KernelThCent.fwd_mats
  have hx := mat_R5 94 (by decide)
  have hy := mat_R5 105 (by decide)
  refine ⟨fun i hi q hq => ?_, fun i hi hcx hcy => ?_⟩
  · have hiE : i < L5.E.length := by rw [E5_length]; exact hi
    have hw := words_of_map E5_words i hiE
    have hl := List.all_eq_true.1 letters5_ok _ (List.getElem_mem hiE)
    unfold el5
    rw [← hw]
    refine CFSG.HardMathSupport.Dickson.I271.list_prod_conj_mem (fun g hg => ?_) q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hg
    have hr' := List.all_eq_true.1 hl r hr
    simp only [letters5, List.elem_eq_mem, List.mem_cons, List.not_mem_nil, or_false,
      decide_eq_true_eq] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · exact letter_conj (t := (19, 114, 2, 4, 4, 2, 2, 4)) (by decide)
    · exact letter_conj (t := (114, 19, 2, 1, 2, 3, 2, 1)) (by decide)
    · exact letter_conj (t := (99, 115, 1, 1, 4, 3, 4, 2)) (by decide)
    · exact letter_conj (t := (115, 99, 4, 4, 2, 2, 1, 2)) (by decide)
  · have hiE : i < L5.E.length := by rw [E5_length]; exact hi
    have hall := all_of_chunkOK _ L5.E 50 60 (by rw [E5_length]) fun k hk' => cn5_all k hk'
    rcases cent5OK_sound hk (hall i hiE) with h1 | h1 | ⟨k, hk5, h1⟩
    · rw [← el5_mat i hiE, ← hx, ← mat_mul, ← mat_mul, hcx] at h1
      exact absurd rfl h1
    · rw [← el5_mat i hiE, ← hy, ← mat_mul, ← mat_mul, hcy] at h1
      exact absurd rfl h1
    · exact ⟨k, hk5, mat_inj (by rw [el5_mat i hiE, h1, mat_pow, mat_c5])⟩

end CertificateChecks.KernelThList

end
