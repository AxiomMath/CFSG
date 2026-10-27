module

public import CFSG.GH74.KGroups.CoverM11Inputs

public section

namespace CertificateChecks.KernelMisc.C5113

open CFSG.GH74.KGroups CFSG.GH74.KGroups.M11 CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier

theorem fw_rels : fw ^ 3 = 1 ∧ fw * sR ^ 4 * fw⁻¹ = sR ^ 4 ∧ fw * sR ^ 2 * fw⁻¹ = sT * sR := by
  decide +kernel

theorem fg_rels : fg1 * sT * fg1⁻¹ = sR ^ 4 ∧ fg2 * sT * fg2⁻¹ = sT * sR ^ 2 := by
  decide +kernel

theorem fw_word : fw = m11gA * m11gB⁻¹ * m11gA * m11gB⁻¹ * m11gA * m11gB * m11gB * m11gA *
    m11gB⁻¹ * m11gA * m11gB⁻¹ * m11gA * m11gB * m11gB * m11gA * m11gB⁻¹ * m11gA * m11gB * m11gB := by
  decide +kernel

theorem fg1_word : fg1 = m11gA * m11gB * m11gA * m11gB⁻¹ * m11gA * m11gB⁻¹ * m11gA * m11gB⁻¹ *
    m11gA * m11gB⁻¹ := by
  decide +kernel

theorem fg2_word : fg2 = m11gB⁻¹ * m11gA * m11gB⁻¹ * m11gA * m11gB * m11gA * m11gB * m11gA *
    m11gB⁻¹ * m11gA * m11gB * m11gA * m11gB⁻¹ := by
  decide +kernel

theorem fg1_word_short : fg1 ≠ m11gA * m11gB * m11gA * m11gB⁻¹ * m11gA * m11gB⁻¹ * m11gA *
    m11gB⁻¹ * m11gA := by
  decide +kernel

theorem mA : m11gA ∈ Q.originalSubgroup := by
  rw [Q_closure]; exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem mB : m11gB ∈ Q.originalSubgroup := by
  rw [Q_closure]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem fw_mem : fw ∈ Q.originalSubgroup := by
  rw [fw_word]; have hA := mA; have hB := mB
  generalize m11gA = a at hA ⊢; generalize m11gB = b at hB ⊢
  have hBi := Subgroup.inv_mem _ hB
  repeat (first | exact hA | exact hB | exact hBi | refine Subgroup.mul_mem _ ?_ ?_)

theorem fg1_mem : fg1 ∈ Q.originalSubgroup := by
  rw [fg1_word]; have hA := mA; have hB := mB
  generalize m11gA = a at hA ⊢; generalize m11gB = b at hB ⊢
  have hBi := Subgroup.inv_mem _ hB
  repeat (first | exact hA | exact hB | exact hBi | refine Subgroup.mul_mem _ ?_ ?_)

theorem fg2_mem : fg2 ∈ Q.originalSubgroup := by
  rw [fg2_word]; have hA := mA; have hB := mB
  generalize m11gA = a at hA ⊢; generalize m11gB = b at hB ⊢
  have hBi := Subgroup.inv_mem _ hB
  repeat (first | exact hA | exact hB | exact hBi | refine Subgroup.mul_mem _ ?_ ?_)

theorem fw_sift : Q.sift fw 0 = true :=
  (mem_iff_sift Q (@Q_ok) fw).1 fw_mem

theorem fg1_sift : Q.sift fg1 0 = true :=
  (mem_iff_sift Q (@Q_ok) fg1).1 fg1_mem

theorem fg2_sift : Q.sift fg2 0 = true :=
  (mem_iff_sift Q (@Q_ok) fg2).1 fg2_mem

end CertificateChecks.KernelMisc.C5113
