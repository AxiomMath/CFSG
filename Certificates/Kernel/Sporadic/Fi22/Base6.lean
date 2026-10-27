module

public import Certificates.Kernel.Sporadic.Fi22.C3147
public import CFSG.Certificates.Kernel.Census.BaseSound

public section

namespace CertificateChecks.KernelSpor.Fi22Base

open CFSG.KC.Census.Base CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Certificates
open CertificateChecks.KernelSpor.Fi22C3147

theorem fi22P_le_strong :
    fi22P ≤ Subgroup.closure {g : Equiv.Perm (Fin 3510) |
      ∃ j < fi22StrongArrs.size, permOfArr 3510 fi22StrongArrs[j]! = g} := by
  have key : ∀ k : Fin 2, fi22GenPerm k ∈ Subgroup.closure {g : Equiv.Perm (Fin 3510) |
      ∃ j < fi22StrongArrs.size, permOfArr 3510 fi22StrongArrs[j]! = g} := by
    intro k
    apply Subgroup.subset_closure
    refine ⟨k, by have := k.2; simp [fi22StrongArrs]; omega, ?_⟩
    rw [fi22StrongArrs_get (by have := k.2; omega)]
    have e := fi22Chain_original_eq ⟨k, k.2⟩
    rw [fi22Chain_original_get, fi22Chain_strong_get] at e
    exact e
  refine (Subgroup.closure_le _).2 ?_
  intro g hg
  change g ∈ (Vector.ofFn fun k : Fin 2 => fi22GenPerm k).toList at hg
  simp only [Vector.toList_ofFn, List.ofFn_succ, List.ofFn_zero, List.mem_cons,
    List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact key 0
  · exact key 1

theorem baseOf_fi22P :
    BaseOf fi22P [0, 1, 2, 3, 6, 4] := by
  refine ⟨by decide, fun g hg hfix => sep6 g (fi22P_le_strong hg) fun t ht hbt => ?_⟩
  have ht6 : t < 6 := by simpa [fi22BaseArr, fi22ChainBase] using ht
  have hmem : fi22BaseArr[t]! ∈ [0, 1, 2, 3, 6, 4] := by
    interval_cases t <;> decide
  exact hfix _ hbt hmem

theorem eq_on_base
    {g g' : Equiv.Perm (Fin 3510)} (hg : g ∈ fi22P)
    (hg' : g' ∈ fi22P)
    (h : ∀ b (hb : b < 3510), b ∈ [0, 1, 2, 3, 6, 4] → (g ⟨b, hb⟩ : ℕ) = (g' ⟨b, hb⟩ : ℕ)) :
    g = g' :=
  eq_of_base baseOf_fi22P hg hg' h

end CertificateChecks.KernelSpor.Fi22Base

end
