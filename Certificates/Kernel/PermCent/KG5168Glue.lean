module

public import Certificates.Kernel.PermCent.KG5168
public import CFSG.Certificates.Kernel.PermCent.CVSound
public import CFSG.Certificates.Kernel.Misc.HeisThree
public import CFSG.GH74.KGroups.L34Aut

public section

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5168

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 CFSG.Certificates CFSG.Sporadic.Schreier
  CFSG.KC.Misc.HeisThree

theorem ev_gA : ev gA = a := by simp only [gA, a, ev_mul, ev_cOf]

theorem ev_gB : ev gB = b := by simp only [gB, b, ev_mul, ev_cOf]

theorem heis : a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a * b ≠ b * a ∧
    (a⁻¹ * b⁻¹ * a * b) * a = a * (a⁻¹ * b⁻¹ * a * b) ∧
    (a⁻¹ * b⁻¹ * a * b) * b = b * (a⁻¹ * b⁻¹ * a * b) ∧ (a⁻¹ * b⁻¹ * a * b) ^ 3 = 1 := by
  have h := kHeis
  simp only [heisC, Bool.and_eq_true, Bool.not_eq_true', powOneC_eq, eq22C_eq,
    decide_eq_true_eq, decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  rw [← ev_gA, ← ev_gB]
  simp only [ev_inv', ev_mul', ev_pow', ← ev_one, ev_eq_iff, ne_eq]
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem gen_mem : ∀ g ∈ [PA, PB, sg0, sg1, sg2], g ∈ QA.originalSubgroup := by
  intro g hg
  rw [QA, certificate_originalSubgroup]
  exact Subgroup.subset_closure hg

theorem a_mem : a ∈ QA.originalSubgroup := by
  simp only [a]
  refine QA.originalSubgroup.mul_mem (QA.originalSubgroup.mul_mem (QA.originalSubgroup.mul_mem
    (QA.originalSubgroup.mul_mem ?_ ?_) ?_) ?_) ?_ <;> exact gen_mem _ (by simp)

theorem b_mem : b ∈ QA.originalSubgroup := by
  simp only [b]
  refine QA.originalSubgroup.mul_mem (QA.originalSubgroup.mul_mem (QA.originalSubgroup.mul_mem
    (QA.originalSubgroup.mul_mem ?_ ?_) ?_) ?_) ?_ <;> exact gen_mem _ (by simp)

theorem P_le_A : QP.originalSubgroup ≤ QA.originalSubgroup := by
  rw [QP_closure, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl <;> exact gen_mem _ (by simp)

theorem H_le_A : Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin 42))) ≤ QA.originalSubgroup := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact a_mem
  · exact b_mem

theorem outer3_mem_QP (σ : Equiv.Perm (Fin 42))
    (hσ : σ ∈ QA.originalSubgroup) (h27 : σ ^ 27 = 1)
    (h9 : 9 ∣ Nat.card ↥(QP.originalSubgroup ⊓
      Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 42))))) :
    σ ∈ QP.originalSubgroup := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := heis
  have hA : ¬ 3 ^ 4 ∣ Nat.card QA.originalSubgroup := by
    rw [card_group QA QA_ok, QA_valid.2]
    norm_num
  have h27' : σ ^ 3 ^ 3 = 1 := by rw [show (3 : ℕ) ^ 3 = 27 by norm_num]; exact h27
  have h9' : 3 ^ 2 ∣ Nat.card ↥(QP.originalSubgroup ⊓
      Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 42)))) := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num]; exact h9
  exact mem_of_nonabelian_sylow P_le_A hA H_le_A (isPGroup_heis h1 h2 h4 h5 h6)
    ⟨a, Subgroup.subset_closure (by simp), b, Subgroup.subset_closure (by simp), h3⟩ hσ h27' h9'

end CFSG.Certificates.Kernel.PkCV.KGrp.K5168
