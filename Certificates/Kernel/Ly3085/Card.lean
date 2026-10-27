
module

public import Certificates.Kernel.Ly3085.CardBase
import all Certificates.Kernel.Ly3085.CardBase

public import Certificates.Kernel.Ly3085.Ord
public import Certificates.Certificate9213
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CertificateChecks.KernelLy

open CFSG.Sporadic.Ly TauCeti

theorem card_JS :
    Nat.card JS = 51765179004000000 := by
  obtain ⟨φ, hφ⟩ := Certificates.certificate9213
  have hfc := Certificates.certificate9120
  revert hfc
  change Finite SporadicName.Ly.presentation.Group ∧
      Nat.card SporadicName.Ly.presentation.Group ≤ 51765179004000000 → _
  rw [presentation_eq]
  rintro ⟨hfin, hcard⟩
  have hJ : JS ≤ φ.range := by
    rw [Subgroup.closure_le]
    intro g hg
    exact hφ g hg
  have : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  have : Finite JS := Finite.of_injective _ (Subgroup.inclusion_injective hJ)
  have h1 : Nat.card JS ≤ Nat.card φ.range := Subgroup.card_le_of_le hJ
  have h2 : Nat.card φ.range ≤ Nat.card Sporadic.Lyons.presentation.Group :=
    Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective
  exact le_antisymm (h1.trans (h2.trans hcard)) (Nat.le_of_dvd Nat.card_pos card_dvd)

end CertificateChecks.KernelLy

end
