module

public import Certificates.Kernel.TwistDce3.ON.Index

public section

namespace CFSG.KD.ONDce3

open CFSG.CosetTable CFSG.Sporadic.Recognition.ONMultiplier

theorem genSub_012 (R : Set (FreeGroup (Fin 4))) :
    genSub R (subsetOf 4 [0, 1, 2]) =
      Subgroup.closure {PresentedGroup.of 0, PresentedGroup.of 1, PresentedGroup.of 2} := by
  have hS : subsetOf 4 [0, 1, 2] = [0, 1, 2] := by decide
  rw [hS]
  refine congrArg Subgroup.closure ?_
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with rfl | rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl) <;> simp

theorem genSub_onCover_eq :
    genSub {r : FreeGroup (Fin 4) | r ∈ onCover.map FreeGroup.mk} (subsetOf 4 [0, 1, 2]) = onHP :=
  genSub_012 _

theorem index_genSub_onCover_le :
    (genSub {r : FreeGroup (Fin 4) | r ∈ onCover.map FreeGroup.mk}
        (subsetOf 4 [0, 1, 2])).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 4) | r ∈ onCover.map FreeGroup.mk}
        (subsetOf 4 [0, 1, 2])).index ≤ 245520 := by
  rw [genSub_onCover_eq]
  exact index_onHP_le

theorem card_onCover_le : Finite (PG 4 onCover) ∧ Nat.card (PG 4 onCover) ≤ 460815505920 := by
  obtain ⟨hf1, hc1⟩ := CertificateChecks.KernelONCover.card_onCover1_le
  obtain ⟨hfi, hidx⟩ := index_genSub_onCover_le
  obtain ⟨hfinH, hsub⟩ := card_genSub_le onCover (subsetOf 4 [0, 1, 2])
  have hfin : Finite (PG 4 onCover) := by
    have : Finite (PG 4 onCover ⧸ genSub {r : FreeGroup (Fin 4) | r ∈ onCover.map FreeGroup.mk}
        (subsetOf 4 [0, 1, 2])) := Subgroup.finite_quotient_of_finiteIndex
    exact Finite.of_subgroup_quotient (genSub _ (subsetOf 4 [0, 1, 2]))
  refine ⟨hfin, ?_⟩
  rw [← (genSub {r : FreeGroup (Fin 4) | r ∈ onCover.map FreeGroup.mk}
    (subsetOf 4 [0, 1, 2])).index_mul_card]
  calc _ ≤ 245520 * 1876896 := Nat.mul_le_mul hidx (hsub.trans hc1)
    _ = 460815505920 := by norm_num

end CFSG.KD.ONDce3

end
