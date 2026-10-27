module

public import CFSG.Sporadic.Recognition.HNMultiplierInputs

public section

namespace CertificateChecks.KernelHNMult

open CFSG.Sporadic.Recognition.HNMultiplier CFSG.LieType.Multipliers
  CFSG.Sporadic.Recognition.CoverRecipe

@[expose] def allWords : List (List (Fin 7 × Bool)) :=
  coverWords hnRels hnCommWord ++ squareWords hnRels ++ (hnPlain1 ++ hnNwords)

theorem incl_all : hnTop.all (fun w => allWords.contains w) = true := by
  decide +kernel

theorem hnIncl : hnTop.all (fun w => hnCoverPlus.contains w) = true := by
  have h := incl_all
  rw [List.all_eq_true] at h ⊢
  intro w hw
  have hw' : w ∈ allWords := List.contains_iff_mem.mp (h w hw)
  apply List.contains_iff_mem.mpr
  unfold allWords at hw'
  rcases List.mem_append.1 hw' with hw' | hw'
  · rcases List.mem_append.1 hw' with hw' | hw'
    · exact List.mem_append_left _ (mem_cover₂Words.2 (Or.inl hw'))
    · exact List.mem_append_left _ (mem_cover₂Words.2 (Or.inr hw'))
  · exact List.mem_append_right _ hw'

end CertificateChecks.KernelHNMult

end
