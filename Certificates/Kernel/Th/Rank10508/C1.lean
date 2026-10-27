module

public import CFSG.Sporadic.Th.Max3.RankInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTh.Rank10508

open CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Max3.Rank

@[expose] def rkP : Fin 12 → Fin 9 → Fin 9 :=
  ![![2, 3, 0, 1, 6, 7, 4, 5, 8], ![2, 3, 0, 1, 7, 6, 5, 4, 8], ![3, 2, 1, 0, 6, 7, 4, 5, 8],
    ![3, 2, 1, 0, 7, 6, 5, 4, 8], ![4, 5, 6, 7, 0, 1, 2, 3, 8], ![4, 5, 7, 6, 0, 1, 3, 2, 8],
    ![5, 4, 6, 7, 1, 0, 2, 3, 8], ![5, 4, 7, 6, 1, 0, 3, 2, 8], ![6, 7, 4, 5, 2, 3, 0, 1, 8],
    ![6, 7, 5, 4, 3, 2, 0, 1, 8], ![7, 6, 4, 5, 2, 3, 1, 0, 8], ![7, 6, 5, 4, 3, 2, 1, 0, 8]]

theorem rkP_eq : ∀ i : Fin 12, ∀ j : Fin 9, rkPerm i j = rkP i j := by decide +kernel

theorem slice0 : ∀ b c d : Fin 9, RkCand (rkTup 0 b c d) →
    ∃ i : Fin 12, ∀ j : Fin 9, rkTup 0 b c d j = rkP i j := by decide +kernel
theorem slice1 : ∀ b c d : Fin 9, RkCand (rkTup 1 b c d) →
    ∃ i : Fin 12, ∀ j : Fin 9, rkTup 1 b c d j = rkP i j := by decide +kernel
theorem slice2 : ∀ b c d : Fin 9, RkCand (rkTup 2 b c d) →
    ∃ i : Fin 12, ∀ j : Fin 9, rkTup 2 b c d j = rkP i j := by decide +kernel
theorem slice3 : ∀ b c d : Fin 9, RkCand (rkTup 3 b c d) →
    ∃ i : Fin 12, ∀ j : Fin 9, rkTup 3 b c d j = rkP i j := by decide +kernel
theorem slice4 : ∀ b c d : Fin 9, RkCand (rkTup 4 b c d) →
    ∃ i : Fin 12, ∀ j : Fin 9, rkTup 4 b c d j = rkP i j := by decide +kernel
theorem slice5 : ∀ b c d : Fin 9, RkCand (rkTup 5 b c d) →
    ∃ i : Fin 12, ∀ j : Fin 9, rkTup 5 b c d j = rkP i j := by decide +kernel
theorem slice6 : ∀ b c d : Fin 9, RkCand (rkTup 6 b c d) →
    ∃ i : Fin 12, ∀ j : Fin 9, rkTup 6 b c d j = rkP i j := by decide +kernel
theorem slice7 : ∀ b c d : Fin 9, RkCand (rkTup 7 b c d) →
    ∃ i : Fin 12, ∀ j : Fin 9, rkTup 7 b c d j = rkP i j := by decide +kernel
theorem slice8 : ∀ b c d : Fin 9, RkCand (rkTup 8 b c d) →
    ∃ i : Fin 12, ∀ j : Fin 9, rkTup 8 b c d j = rkP i j := by decide +kernel

theorem conj1 : ∀ a b c d : Fin 9, RkCand (rkTup a b c d) →
    ∃ i : Fin 12, ∀ j : Fin 9, rkTup a b c d j = rkPerm i j := by
  intro a b c d h
  have key : ∃ i : Fin 12, ∀ j : Fin 9, rkTup a b c d j = rkP i j := by
    fin_cases a
    · exact slice0 b c d h
    · exact slice1 b c d h
    · exact slice2 b c d h
    · exact slice3 b c d h
    · exact slice4 b c d h
    · exact slice5 b c d h
    · exact slice6 b c d h
    · exact slice7 b c d h
    · exact slice8 b c d h
  obtain ⟨i, hi⟩ := key
  exact ⟨i, fun j => by rw [hi j, rkP_eq]⟩

end CertificateChecks.KernelTh.Rank10508

end
