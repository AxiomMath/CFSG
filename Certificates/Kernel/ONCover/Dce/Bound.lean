module

public import Certificates.Kernel.ONCover.Dce.Index

public section

namespace CFSG.KD.ONCoverDce3

open CFSG.CosetTable CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCover

theorem genSub_mainWs_eq :
    genSub {r : FreeGroup (Fin 4) | r ∈ mainWs.map FreeGroup.mk} (subsetOf 4 [0, 1, 2]) = onHP := by
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

theorem index_genSub_mainWs_le :
    (genSub {r : FreeGroup (Fin 4) | r ∈ mainWs.map FreeGroup.mk}
        (subsetOf 4 [0, 1, 2])).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 4) | r ∈ mainWs.map FreeGroup.mk}
        (subsetOf 4 [0, 1, 2])).index ≤ 736560 := by
  rw [genSub_mainWs_eq]
  exact index_onHP_le

theorem card_mainWs_le : Finite (PG 4 mainWs) ∧ Nat.card (PG 4 mainWs) ≤ 1382446517760 := by
  obtain ⟨hf1, hc1⟩ := CertificateChecks.KernelONCover.card_mainWs₁_le
  obtain ⟨hfi, hidx⟩ := index_genSub_mainWs_le
  obtain ⟨hfinH, hsub⟩ := card_genSub_le mainWs (subsetOf 4 [0, 1, 2])
  have hfin : Finite (PG 4 mainWs) := by
    have : Finite (PG 4 mainWs ⧸ genSub {r : FreeGroup (Fin 4) | r ∈ mainWs.map FreeGroup.mk}
        (subsetOf 4 [0, 1, 2])) := Subgroup.finite_quotient_of_finiteIndex
    exact Finite.of_subgroup_quotient (genSub _ (subsetOf 4 [0, 1, 2]))
  refine ⟨hfin, ?_⟩
  rw [← (genSub {r : FreeGroup (Fin 4) | r ∈ mainWs.map FreeGroup.mk}
    (subsetOf 4 [0, 1, 2])).index_mul_card]
  calc _ ≤ 736560 * 1876896 := Nat.mul_le_mul hidx (hsub.trans hc1)
    _ = 1382446517760 := by norm_num

end CFSG.KD.ONCoverDce3

end
