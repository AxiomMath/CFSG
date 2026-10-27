module

public import CFSG.Sporadic.Bridge.Co2Surj
public import CFSG.Sporadic.Co2Cert.Faithful
public import Certificates.Certificate9101
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CertificateChecks.KernelSpor.Co2Card

open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen CFSG.Sporadic.SmallF2 TauCeti

theorem card_le_of_closure {G : Type*} [Group G] (P : GroupPresentation)
    (hP : P.generatorCount = 2) {x y : G} (hclosure : Subgroup.closure ({x, y} : Set G) = ⊤)
    (hrel : ∀ v ∈ P.relatorLetters, wordProd (img2 x y) v = 1) [Finite P.Group] :
    Nat.card G ≤ Nat.card P.Group := by
  have hsurj : Function.Surjective (presHom P (img2 x y) hrel) := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hclosure, Subgroup.closure_le]
    rintro g (h | h)
    · exact ⟨presGen P 0, by
        rw [presHom_presGen P (img2 x y) hrel (by omega), h]
        simp [img2]⟩
    · rw [Set.mem_singleton_iff] at h
      exact ⟨presGen P 1, by
        rw [presHom_presGen P (img2 x y) hrel (by omega), h]
        simp [img2]⟩
  exact Nat.card_le_card_of_surjective _ hsurj

theorem card_JD_le :
    Nat.card Co2.JD ≤ 42305421312000 := by
  have e : SporadicName.Co2.presentation = Sporadic.co2Presentation := rfl
  have hfin : Finite SporadicName.Co2.presentation.Group := Certificates.certificate9101.1
  have hcard : Nat.card SporadicName.Co2.presentation.Group ≤ 42305421312000 :=
    Certificates.certificate9101.2
  rw [e] at hfin hcard
  exact (card_le_of_closure Sporadic.co2Presentation Co2.generatorCount_eq
    (closure_ab CFSG.Sporadic.Co2.Native.co2Data) Co2.relators_eval).trans hcard

theorem card_co2P_le :
    Nat.card CFSG.Sporadic.Co2Cert.co2P ≤ 42305421312000 := by
  rw [← Nat.card_congr CFSG.Sporadic.Co2Cert.co2PermEquiv.toEquiv,
    Nat.card_congr Co2.nativeEquiv.toEquiv]
  exact card_JD_le

end CertificateChecks.KernelSpor.Co2Card

end
