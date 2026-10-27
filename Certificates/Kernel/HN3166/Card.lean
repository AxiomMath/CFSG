
module

public import Certificates.Kernel.HN3166.CardBase
import all Certificates.Kernel.HN3166.CardBase

public import Certificates.Kernel.HN3166.Ord
public import CFSG.Sporadic.Presentation.HNInputs
public import Certificates.Certificate9208
public import CFSG.Sporadic.Presentation.HN
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CertificateChecks.KernelHN

open CFSG.Sporadic.F5

local notation "Dt" => CFSG.Sporadic.HN.Native.hnData

theorem card_J :
    Nat.card (J Dt) = 273030912000000 := by
  obtain ⟨φ, hφ⟩ := Certificates.certificate9208
  have hfc := CFSG.Sporadic.Presentation.HN.finite_card_le
  revert hfc
  change Finite TauCeti.SporadicName.HN.presentation.Group ∧
      Nat.card TauCeti.SporadicName.HN.presentation.Group ≤ 273030912000000 → _
  rw [presentation_eq]
  rintro ⟨hfin, hcard⟩
  have : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  have : Finite (J Dt) := Finite.of_injective _ (Subgroup.inclusion_injective hφ)
  have h1 : Nat.card (J Dt) ≤ Nat.card φ.range := Subgroup.card_le_of_le hφ
  have h2 : Nat.card φ.range ≤ Nat.card TauCeti.Sporadic.hnPresentation.Group :=
    Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective
  exact le_antisymm (h1.trans (h2.trans hcard)) (Nat.le_of_dvd Nat.card_pos card_dvd)

end CertificateChecks.KernelHN

end
