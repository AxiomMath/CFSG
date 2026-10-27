module

public import Certificates.Kernel.Misc.GL52.ClsFacts

public section

namespace CertificateChecks.KernelMisc.GL52K

open CFSG.KC.Misc.GLM CFSG.Literature.GL52 CFSG.GH74.KGroups

theorem map_data {β : Type*} (F : ℕ × ℕ × ℕ × ℕ → β) :
    rsAll.map (fun r => F (orderOf r, fixCount r, invS (r : Mat), clsSize r)) = dataL.map F := by
  rw [← data, List.map_map]
  rfl

theorem rs_nodup : (rsAll.map fun g : G => invS (g : Mat)).Nodup := by
  have h := map_data (fun t => t.2.2.1)
  simp only at h
  rw [h]
  decide

theorem rs_sum : (rsAll.map clsSize).sum = Nat.card G := by
  have h := map_data (fun t => t.2.2.2)
  simp only at h
  rw [h, card_G]
  decide

theorem count_by (Q : ℕ → ℕ → Bool) :
    Nat.card {g : G // Q (orderOf g) (fixCount g) = true} =
      (dataL.map fun t => if Q t.1 t.2.1 then t.2.2.2 else 0).sum := by
  rw [card_of_classes (fun g : G => invS (g : Mat)) invS_conj rsAll rs_nodup rs_sum
    (fun g => Q (orderOf g) (fixCount g) = true) (fun g x h => by
      rwa [orderOf_conj', fixCount_conj]), filter_map_sum]
  have h := map_data (fun t => if Q t.1 t.2.1 then t.2.2.2 else 0)
  simp only at h
  simp only [decide_eq_true_eq]
  rw [h]

theorem count_ord (k : ℕ) :
    Nat.card {g : G // orderOf g = k} =
      (dataL.map fun t => if t.1 == k then t.2.2.2 else 0).sum := by
  rw [← count_by (fun o _ => o == k)]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp)

theorem count_ord_fix (k m : ℕ) :
    Nat.card {g : G // orderOf g = k ∧ fixCount g = m} =
      (dataL.map fun t => if (t.1 == k && t.2.1 == m) then t.2.2.2 else 0).sum := by
  rw [← count_by (fun o f => o == k && f == m)]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp)

theorem centralizer_eq (x : G) : Nat.card (Subgroup.centralizer {x}) = centCard (⊤ : Subgroup G) x :=
  Nat.card_congr (Equiv.subtypeEquivRight fun g => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp)

theorem conj_r0 :
    Nat.card {g : G // (∃ r ∈ r0Elts, g * glTau2 = r * g) ∧ ∃ r ∈ r0Elts, g * glTauB = r * g} =
      72 := by
  rw [card_exists_pairs _ _ _ r0_nodup]
  exact r0_sum

open Certificates in
open CFSG CFSG.Literature CFSG.Literature.GL52 in
theorem facts : Nat.card {g : G // orderOf g = 2} = 6975
    ∧ Nat.card {g : G // orderOf g = 2 ∧ fixCount g = 15} = 465
    ∧ Nat.card {g : G // orderOf g = 2 ∧ fixCount g = 7} = 6510
    ∧ Nat.card {g : G // orderOf g = 3} = 75392
    ∧ Nat.card {g : G // orderOf g = 3 ∧ fixCount g = 1} = 55552
    ∧ Nat.card {g : G // orderOf g = 3 ∧ fixCount g = 7} = 19840
    ∧ Nat.card (Subgroup.centralizer {glT0}) = 21504
    ∧ Nat.card (Subgroup.centralizer {glU0}) = 1536
    ∧ Nat.card (Subgroup.centralizer {glTau1}) = 180
    ∧ Nat.card (Subgroup.centralizer {glTau2}) = 504
    ∧ Nat.card {g : G // g * glTau2 = glTau2 * g ∧ g * glTauB = glTauB * g} = 9
    ∧ Nat.card (Subgroup.centralizer {glF5}) = 15
    ∧ Nat.card {g : G // (∃ r ∈ r0Elts, g * glTau2 = r * g) ∧ ∃ r ∈ r0Elts, g * glTauB = r * g} =
      72
    ∧ Nat.card {g : G // orderOf g = 5} = 666624
    ∧ Nat.card {g : G // orderOf g = 7} = 476160
    ∧ Nat.card {g : G // orderOf g = 31} = 1935360 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, cZ0Card, ?_, conj_r0, ?_, ?_, ?_⟩
  · rw [count_ord]; decide
  · rw [count_ord_fix]; decide
  · rw [count_ord_fix]; decide
  · rw [count_ord]; decide
  · rw [count_ord_fix]; decide
  · rw [count_ord_fix]; decide
  · rw [centralizer_eq, cent0]
  · rw [centralizer_eq, cent1]
  · rw [centralizer_eq, cent3]
  · rw [centralizer_eq, cent2]
  · rw [centralizer_eq, cent7]
  · rw [count_ord]; decide
  · rw [count_ord]; decide
  · rw [count_ord]; decide

end CertificateChecks.KernelMisc.GL52K

end
