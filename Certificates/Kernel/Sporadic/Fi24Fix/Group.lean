
module

public import Certificates.Kernel.Sporadic.Fi24Fix.Tabs
public import CFSG.Sporadic.Bridge.Common
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all CFSG.Sporadic.Bridge.Common
public import CFSG.Certificates.Kernel.Spor.Fi24FixCoset

public section

namespace CertificateChecks.KernelFi24Fix

open CertificateChecks.KernelFi24 CertificateChecks.KernelCo2 TauCeti TauCeti.Sporadic
  CFSG.Sporadic.Bridge CFSG.KC.Fi24FixC CFSG.KC.Fi24FixS

noncomputable abbrev E : Subgroup Fi24AutomorphismGroup := commutator Fi24AutomorphismGroup

theorem g0_of {j : ℕ} (h : j < 12) : g0 j = PresentedGroup.of ⟨j, h⟩ := pgen_lt _ h

theorem g0_mul_self (j : ℕ) : g0 j * g0 j = 1 := by
  rcases Nat.lt_or_ge j 12 with h | h
  · rw [g0_of h]
    exact fi24AutomorphismGroup_of_mul_of_self _
  · have : g0 j = 1 := by simp [g0, pgen, Nat.not_lt.2 h]
    rw [this, mul_one]

theorem g0_inv (j : ℕ) : (g0 j)⁻¹ = g0 j := inv_eq_of_mul_eq_one_right (g0_mul_self j)

theorem g0_mul_self_mul (j : ℕ) (z : Fi24AutomorphismGroup) : g0 j * (g0 j * z) = z := by
  rw [← mul_assoc, g0_mul_self, one_mul]

theorem parity_g0 {j : ℕ} (h : j < 12) : fi24ParityHom (g0 j) = Multiplicative.ofAdd 1 := by
  rw [g0_of h, fi24ParityHom_of]

theorem mem_E_iff (q : Fi24AutomorphismGroup) : q ∈ E ↔ fi24ParityHom q = 1 := by
  rw [E, commutator_fi24AutomorphismGroup_eq_ker_fi24ParityHom, MonoidHom.mem_ker]

theorem a_not_mem_E : g0 0 ∉ E := by
  rw [mem_E_iff, parity_g0 (by norm_num)]
  decide

theorem mem_E_or (q : Fi24AutomorphismGroup) : q ∈ E ∨ g0 0 * q ∈ E := by
  rw [mem_E_iff, mem_E_iff, map_mul, parity_g0 (by norm_num)]
  generalize fi24ParityHom q = t
  revert t
  decide

theorem pair_mem_E {i j : ℕ} (hi : i < 12) (hj : j < 12) : g0 i * g0 j ∈ E := by
  rw [mem_E_iff, map_mul, parity_g0 hi, parity_g0 hj]
  decide

theorem a_mem_H1 : g0 0 ∈ H1 := Subgroup.subset_closure ⟨0, Or.inl (by norm_num), rfl⟩

noncomputable abbrev H0 : Subgroup Fi24AutomorphismGroup :=
  Subgroup.closure ((fun j => g0 0 * g0 (hgen j)) '' {j | j < 9})

theorem hgen_lt {j : ℕ} (hj : j < 9) : hgen j < 12 := by
  unfold hgen
  split_ifs <;> omega

theorem H0_le_E : H0 ≤ E := by
  rw [Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact pair_mem_E (by norm_num) (hgen_lt hj)

theorem conj_a_H0 {m : Fi24AutomorphismGroup} (hm : m ∈ H0) : g0 0 * m * (g0 0)⁻¹ ∈ H0 := by
  induction hm using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    have e : g0 0 * (g0 0 * g0 (hgen j)) * (g0 0)⁻¹ = (g0 0 * g0 (hgen j))⁻¹ := by
      rw [g0_mul_self_mul, mul_inv_rev, g0_inv, g0_inv]
    rw [e]
    exact H0.inv_mem (Subgroup.subset_closure ⟨j, hj, rfl⟩)
  | one => simp
  | mul x y _ _ hx hy =>
    have e : g0 0 * (x * y) * (g0 0)⁻¹ = (g0 0 * x * (g0 0)⁻¹) * (g0 0 * y * (g0 0)⁻¹) := by group
    rw [e]
    exact H0.mul_mem hx hy
  | inv x _ hx =>
    have e : g0 0 * x⁻¹ * (g0 0)⁻¹ = (g0 0 * x * (g0 0)⁻¹)⁻¹ := by group
    rw [e]
    exact H0.inv_mem hx

theorem H1_split {h : Fi24AutomorphismGroup} (hh : h ∈ H1) : h ∈ H0 ∨ g0 0 * h ∈ H0 := by
  induction hh using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    right
    rcases Nat.eq_zero_or_pos g with rfl | hg0
    · rw [g0_mul_self]
      exact H0.one_mem
    · refine Subgroup.subset_closure ⟨if g = 10 then 8 else g - 1, ?_, ?_⟩
      · change (if g = 10 then 8 else g - 1) < 9
        rcases hg with hg | hg <;> split_ifs <;> omega
      · change g0 0 * g0 (hgen (if g = 10 then 8 else g - 1)) = g0 0 * g0 g
        congr 2
        unfold hgen
        rcases hg with hg | hg <;> split_ifs <;> omega
  | inv_mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    rw [g0_inv]
    right
    rcases Nat.eq_zero_or_pos g with rfl | hg0
    · rw [g0_mul_self]
      exact H0.one_mem
    · refine Subgroup.subset_closure ⟨if g = 10 then 8 else g - 1, ?_, ?_⟩
      · change (if g = 10 then 8 else g - 1) < 9
        rcases hg with hg | hg <;> split_ifs <;> omega
      · change g0 0 * g0 (hgen (if g = 10 then 8 else g - 1)) = g0 0 * g0 g
        congr 2
        unfold hgen
        rcases hg with hg | hg <;> split_ifs <;> omega
  | one => exact Or.inl H0.one_mem
  | mul x y _ _ hx hy =>
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (H0.mul_mem hx hy)
    · right
      have e : g0 0 * (x * y) = (g0 0 * x * (g0 0)⁻¹) * (g0 0 * y) := by group
      rw [e]
      exact H0.mul_mem (conj_a_H0 hx) hy
    · right
      rw [← mul_assoc]
      exact H0.mul_mem hx hy
    · left
      have e : x * y = (g0 0 * (g0 0 * x) * (g0 0)⁻¹) * (g0 0 * y) := by
        rw [g0_mul_self_mul, g0_inv, mul_assoc, g0_mul_self_mul]
      rw [e]
      exact H0.mul_mem (conj_a_H0 hx) hy

theorem H1_inf_E {h : Fi24AutomorphismGroup} (hh : h ∈ H1) (hE : h ∈ E) : h ∈ H0 := by
  rcases H1_split hh with h1 | h1
  · exact h1
  · exfalso
    apply a_not_mem_E
    have : g0 0 = (g0 0 * h) * h⁻¹ := by group
    rw [this]
    exact E.mul_mem (H0_le_E h1) (E.inv_mem hE)

theorem gcount : fi24PrimePresentation.generatorCount = 11 := by
  simp [GroupPresentation.generatorCount, fi24PrimePresentation_generatorNames]

theorem iso_presGen {k : ℕ} (hk : k < 11) :
    (fi24PrimeGroupMulEquivCommutator (presGen fi24PrimePresentation k) : Fi24AutomorphismGroup) =
      g0 0 * g0 (k + 1) := by
  have hg : k < fi24PrimePresentation.generatorCount := by
    rw [gcount]
    exact hk
  rw [presGen, dif_pos hg, g0_of (by norm_num), g0_of (by omega)]
  exact coe_fi24PrimeGroupMulEquivCommutator_of ⟨k, hk⟩

end CertificateChecks.KernelFi24Fix

end
