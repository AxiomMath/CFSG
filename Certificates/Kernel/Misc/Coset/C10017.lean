module

public import CFSG.LieType.Multipliers.U62KernelInputs
public import Certificates.Kernel.Misc.Coset.XU62K
public import Certificates.Kernel.Misc.Coset.XU62KA.All

public section

namespace CertificateChecks.KernelMiscCoset.C10017

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U62
  CFSG.Certificates.CosetEnumeration

theorem t : coverWs.map encW = CFSG.KBRoute.XU62K.rels := by decide +kernel
theorem w : CFSG.KBRoute.XU62K.T1.words = (subsetOf 5 [0, 1, 2, 3]).map fun x => [(x.val, true)] := by
  decide +kernel
theorem hR : codes rels = CFSG.KAct.XU62K.R := by decide +kernel
theorem hW : codes ((List.finRange 5).map fun i => (i, false) :: commWords (coverPairs i)) ++
    codes fixWords = CFSG.KAct.XU62K.W := by decide +kernel
theorem hM : codes moveWords = CFSG.KAct.XU62K.M := by decide +kernel

theorem hom : ∃ (E : Type) (_ : Group E) (ψ : PG 5 coverWs →* E),
    (∀ u ∈ fixWords, ψ (PresentedGroup.mk _ (FreeGroup.mk u)) = 1) ∧
      ∀ u ∈ moveWords, ψ (PresentedGroup.mk _ (FreeGroup.mk u)) ≠ 1 := by
  have hpt := Act.coverPointOK_sound rels (fun i => commWords (coverPairs i)) fixWords hR hW
    (Act.coverPointOK_of_allR CFSG.KAct.XU62K.all)
  have hm : Act.movesOK CFSG.KAct.XU62K.A (Nat.add 5 5) (codes moveWords) = true := by
    rw [hM]
    exact CFSG.KAct.XU62K.moves
  refine Act.movesOK_sound coverWs fixWords ?_ (by norm_num) hpt moveWords hm
  simp only [codes, List.map_append]

theorem index : (genSub {r : FreeGroup (Fin 5) | r ∈ coverWs.map FreeGroup.mk}
      (subsetOf 5 [0, 1, 2, 3])).FiniteIndex ∧
    (genSub {r : FreeGroup (Fin 5) | r ∈ coverWs.map FreeGroup.mk}
      (subsetOf 5 [0, 1, 2, 3])).index ≤ 8064 := by
  have h := XU62K.t1
  unfold CFSG.KBRoute.XU62K.T1.ok at h
  exact genSub_index_le_of_tableOk coverWs t h (by norm_num) CFSG.KBRoute.XU62K.top _ w

end CertificateChecks.KernelMiscCoset.C10017

end
