module

public import Certificates.Kernel.E8K.U33Checks
public import Certificates.Kernel.E8K.L33Checks
public import CFSG.Certificates.Kernel.E8KSound
public import CFSG.GH74.KGroups.U33
public import CFSG.GH74.KGroups.L33
import CFSG.GH74.KGroups.AutModelIndexTwo

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelE8K.Glue

open Equiv CFSG.KC.Ord CFSG.KC.LQT CFSG.KC.Misc.Clos CFSG.KC.Misc.M22 CFSG.KC.E8K
open CFSG.GH74.KGroups CFSG.GroupTheory

theorem index_two {n : ℕ} {Q K : Subgroup (Perm (Fin n))} (hKQ : K ≤ Q)
    (hcard : Nat.card Q = 2 * Nat.card K) :
    (∀ x ∈ Q, ∀ y ∈ Q, x ∉ K → y ∉ K → x * y ∈ K) ∧ ¬ Q ≤ K := by
  have hK0 : 0 < Nat.card K := Nat.card_pos
  have hH : Nat.card (K.subgroupOf Q) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKQ).toEquiv
  have hidx : (K.subgroupOf Q).index = 2 := by
    have h := (K.subgroupOf Q).card_mul_index
    rw [hH, hcard, mul_comm 2] at h
    exact Nat.eq_of_mul_eq_mul_left hK0 h
  refine ⟨fun x hx y hy hxK hyK => ?_, fun hle => ?_⟩
  · have h := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)
    simp only [Subgroup.mem_subgroupOf] at h
    exact h.2 (iff_of_false hxK hyK)
  · have h := Subgroup.card_le_of_le hle
    omega

theorem pow64 : (64 : ℕ) = 2 ^ Nat.log 2 64 := by
  rw [show (64 : ℕ) = 2 ^ 6 by norm_num, Nat.log_pow (by norm_num)]

theorem pow32 : (32 : ℕ) = 2 ^ Nat.log 2 32 := by
  rw [show (32 : ℕ) = 2 ^ 5 by norm_num, Nat.log_pow (by norm_num)]

section U33

open CertificateChecks.KernelE8K.U33

theorem hAU : ∀ a < [U33.pa, U33.pb, U33.sg0].length,
    nthL A a = pcode ([U33.pa, U33.pb, U33.sg0].getD a 1) := by
  decide +kernel

theorem QU_eq : U33.QA.originalSubgroup = Subgroup.closure {g | g ∈ [U33.pa, U33.pb, U33.sg0]} := by
  rw [U33.QA_closure]
  congr 1
  ext g
  simp


theorem u33 : E8GenFacts ↥U33.QA.originalSubgroup ∧
    ∀ B : Subgroup (Perm (Fin 28)), B ≤ U33.QP.originalSubgroup →
      (∀ b ∈ B, b ^ 2 = 1) → ¬ 8 ≤ Nat.card B := by
  have hn : 28 ≤ 32 := by norm_num
  have hcardQ : Nat.card (Subgroup.closure {g | g ∈ [U33.pa, U33.pb, U33.sg0]}) = 12096 := by
    rw [← QU_eq]
    exact (card_group U33.QA U33.QA_ok).trans U33.QA_valid.2
  have hodd : 12096 / 64 % 2 = 1 := by norm_num
  have hg := (allN_iff _ _).1 genB
  have ht := (allN_iff _ _).1 treeB
  have hs := (allN_iff _ _).1 sortB
  have hc := (allN_iff _ _).1 closedB
  have hi := (allN_iff _ _).1 invB
  have hp := (allN_iff _ _).1 pairB
  have htr := (allN_iff _ _).1 triB
  refine ⟨?_, fun B hB hB2 h8 => ?_⟩
  · rw [QU_eq]
    exact e8GenFacts_of_checks hn _ hAU (by norm_num) pow64 hcardQ hodd hg ht hs hc hi hp htr witB
  · have hKQ : U33.QP.originalSubgroup ≤ Subgroup.closure {g | g ∈ [U33.pa, U33.pb, U33.sg0]} := by
      rw [← QU_eq, U33.QP_closure, U33.QA_closure]
      exact U33.P_le_A
    have hcardK : Nat.card (Subgroup.closure {g | g ∈ [U33.pa, U33.pb, U33.sg0]}) =
        2 * Nat.card U33.QP.originalSubgroup := by
      rw [hcardQ, card_group U33.QP U33.QP_ok, U33.QP_valid.2]
    obtain ⟨h2, hQK⟩ := index_two hKQ hcardK
    obtain ⟨M, hMP, hMA⟩ := U33.autModel (MulEquiv.refl U33.QP.originalSubgroup)
    have hPQ : ∀ g ∈ Subgroup.closure {g | g ∈ [U33.pa, U33.pb, U33.sg0]},
        ∀ x ∈ U33.QP.originalSubgroup, g * x * g⁻¹ ∈ U33.QP.originalSubgroup := by
      intro g hg x hx
      rw [← QU_eq, ← hMA] at hg
      rw [← hMP] at hx ⊢
      exact AutModel.conj_mem M hg hx
    have hgP : ∀ j < [U33.pa, U33.pb, U33.sg0].length, j ≠ 2 →
        [U33.pa, U33.pb, U33.sg0].getD j 1 ∈ U33.QP.originalSubgroup := by
      intro j hj hj2
      have hj3 : j < 3 := hj
      rw [U33.QP_closure]
      interval_cases j
      · exact U33.pa_mem
      · exact U33.pb_mem
      · exact absurd rfl hj2
    have hsP : [U33.pa, U33.pb, U33.sg0].getD 2 1 ∉ U33.QP.originalSubgroup := by
      intro h
      apply hQK
      rw [Subgroup.closure_le]
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hg
      rcases hg with rfl | rfl | rfl
      · exact hgP 0 (by norm_num) (by norm_num)
      · exact hgP 1 (by norm_num) (by norm_num)
      · exact h
    exact not_le_of_checks hn _ hAU (by norm_num) pow64 hcardQ hodd hg ht hs hc hi hp htr witB
      (by norm_num) hPQ hgP hsP h2 B (hB.trans hKQ) hB2 h8 hB

end U33

section L33

open CertificateChecks.KernelE8K.L33

theorem hAL : ∀ a < [CFSG.GH74.KGroups.L33.PA, CFSG.GH74.KGroups.L33.PB, L33.sg0].length,
    nthL A a = pcode ([CFSG.GH74.KGroups.L33.PA, CFSG.GH74.KGroups.L33.PB, L33.sg0].getD a 1) := by
  decide +kernel

theorem QL_eq : L33.QA.originalSubgroup =
    Subgroup.closure {g | g ∈ [CFSG.GH74.KGroups.L33.PA, CFSG.GH74.KGroups.L33.PB, L33.sg0]} := by
  rw [L33.QA, CFSG.Sporadic.Schreier.certificate_originalSubgroup]


theorem l33 : E8GenFacts ↥L33.QA.originalSubgroup ∧
    ∀ B : Subgroup (Perm (Fin 26)), B ≤ L33.QP.originalSubgroup →
      (∀ b ∈ B, b ^ 2 = 1) → ¬ 8 ≤ Nat.card B := by
  have hn : 26 ≤ 32 := by norm_num
  have hcardQ : Nat.card (Subgroup.closure {g | g ∈ [CFSG.GH74.KGroups.L33.PA, CFSG.GH74.KGroups.L33.PB, L33.sg0]}) = 11232 := by
    rw [← QL_eq]
    exact (card_group L33.QA L33.QA_ok).trans L33.QA_valid.2
  have hodd : 11232 / 32 % 2 = 1 := by norm_num
  have hg := (allN_iff _ _).1 genB
  have ht := (allN_iff _ _).1 treeB
  have hs := (allN_iff _ _).1 sortB
  have hc := (allN_iff _ _).1 closedB
  have hi := (allN_iff _ _).1 invB
  have hp := (allN_iff _ _).1 pairB
  have htr := (allN_iff _ _).1 triB
  refine ⟨?_, fun B hB hB2 h8 => ?_⟩
  · rw [QL_eq]
    exact e8GenFacts_of_checks hn _ hAL (by norm_num) pow32 hcardQ hodd hg ht hs hc hi hp htr witB
  · have hPAm : CFSG.GH74.KGroups.L33.PA ∈ Subgroup.closure ({CFSG.GH74.KGroups.L33.PA, CFSG.GH74.KGroups.L33.PB} : Set (Perm (Fin 26))) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hPBm : CFSG.GH74.KGroups.L33.PB ∈ Subgroup.closure ({CFSG.GH74.KGroups.L33.PA, CFSG.GH74.KGroups.L33.PB} : Set (Perm (Fin 26))) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    have hKQ : L33.QP.originalSubgroup ≤ Subgroup.closure {g | g ∈ [CFSG.GH74.KGroups.L33.PA, CFSG.GH74.KGroups.L33.PB, L33.sg0]} := by
      rw [L33.QP_closure, Subgroup.closure_le]
      intro x hx
      apply Subgroup.subset_closure
      rcases hx with rfl | rfl <;> simp
    have hcardK : Nat.card (Subgroup.closure {g | g ∈ [CFSG.GH74.KGroups.L33.PA, CFSG.GH74.KGroups.L33.PB, L33.sg0]}) =
        2 * Nat.card L33.QP.originalSubgroup := by
      rw [hcardQ, card_group L33.QP L33.QP_ok, L33.QP_valid.2]
    obtain ⟨h2, hQK⟩ := index_two hKQ hcardK
    obtain ⟨M, hMP, hMA⟩ := L33.autModel (MulEquiv.refl L33.QP.originalSubgroup)
    have hPQ : ∀ g ∈ Subgroup.closure {g | g ∈ [CFSG.GH74.KGroups.L33.PA, CFSG.GH74.KGroups.L33.PB, L33.sg0]},
        ∀ x ∈ L33.QP.originalSubgroup, g * x * g⁻¹ ∈ L33.QP.originalSubgroup := by
      intro g hg x hx
      rw [← QL_eq, ← hMA] at hg
      rw [← hMP] at hx ⊢
      exact AutModel.conj_mem M hg hx
    have hgP : ∀ j < [CFSG.GH74.KGroups.L33.PA, CFSG.GH74.KGroups.L33.PB, L33.sg0].length, j ≠ 2 →
        [CFSG.GH74.KGroups.L33.PA, CFSG.GH74.KGroups.L33.PB, L33.sg0].getD j 1 ∈ L33.QP.originalSubgroup := by
      intro j hj hj2
      have hj3 : j < 3 := hj
      rw [L33.QP_closure]
      interval_cases j
      · exact hPAm
      · exact hPBm
      · exact absurd rfl hj2
    have hsP : [CFSG.GH74.KGroups.L33.PA, CFSG.GH74.KGroups.L33.PB, L33.sg0].getD 2 1 ∉ L33.QP.originalSubgroup := by
      intro h
      apply hQK
      rw [Subgroup.closure_le]
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hg
      rcases hg with rfl | rfl | rfl
      · exact hgP 0 (by norm_num) (by norm_num)
      · exact hgP 1 (by norm_num) (by norm_num)
      · exact h
    exact not_le_of_checks hn _ hAL (by norm_num) pow32 hcardQ hodd hg ht hs hc hi hp htr witB
      (by norm_num) hPQ hgP hsP h2 B (hB.trans hKQ) hB2 h8 hB

end L33

end CertificateChecks.KernelE8K.Glue

end
