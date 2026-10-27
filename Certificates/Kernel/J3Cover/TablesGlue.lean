module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3CoverInputs
public import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import Certificates.Kernel.CosPres.F291370
import Certificates.Kernel.CosPres.F291370AF

public section

namespace CertificateChecks.KernelJ3Cover

open CFSG.CosetTable CFSG.KC.MiscCoset
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3Cover

private def wsA : List (List (Fin 3 × Bool)) :=
  CFSG.KBRoute.F291370a.rels.map fun w =>
    w.filterMap fun l => if h : l.1 < 3 then some (⟨l.1, h⟩, l.2) else none

private theorem wsA_enc : wsA.map encW = CFSG.KBRoute.F291370a.rels := by decide +kernel

private theorem wsA_words :
    CFSG.KBRoute.F291370a.T1.words = (subsetOf 3 [0, 1]).map fun x => [(x.val, true)] := by
  decide +kernel

private theorem wsA_restrict :
    (restrictWords (subsetOf 3 [0, 1]) wsA).map encW = CFSG.KBRoute.F291370b.rels := by
  decide +kernel

private theorem wsA_perm : wsA.Perm cover := by decide +kernel

theorem card_coverS_le : Finite (PG 3 coverS) ∧ Nat.card (PG 3 coverS) ≤ 150698880 := by
  have ha := CFSG.KBFact.F291370a
  rw [← wsA_enc, wsA_words] at ha
  have hb := CFSG.KBFact.F291370b
  rw [← wsA_restrict] at hb
  obtain ⟨f, c⟩ := TableFact.card_restrict wsA (by decide) (subsetOf 3 [0, 1]) (by decide) ha hb
  have e : {r : FreeGroup (Fin 3) | r ∈ wsA.map FreeGroup.mk} =
      {r : FreeGroup (Fin 3) | r ∈ coverS.map FreeGroup.mk} :=
    Set.ext fun r => ((wsA_perm.trans (List.mergeSort_perm _ _).symm).map _).mem_iff
  have hc : Finite (PresentedGroup {r : FreeGroup (Fin 3) | r ∈ wsA.map FreeGroup.mk}) ∧
      Nat.card (PresentedGroup {r : FreeGroup (Fin 3) | r ∈ wsA.map FreeGroup.mk}) ≤
        150698880 := ⟨f, c.trans (by norm_num)⟩
  rw [e] at hc
  exact hc

end CertificateChecks.KernelJ3Cover

end
