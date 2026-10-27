module

public import Certificates.Kernel.VecCert.Co2
public import Certificates.Kernel.VecCert.Bound
public import Certificates.Kernel.Sporadic.Co2.Rels
public import CFSG.Sporadic.Presentation.Co2
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Certificates.CentralizerPresented
public import CFSG.Sporadic.Presentation.Common

public section

namespace CertificateChecks.KernelVec.Co2

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

theorem gens : TauCeti.Sporadic.co2Presentation.generatorCount = 2 := by
  simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.co2Presentation_generatorNames]

theorem card_J_le :
    Nat.card (J CFSG.Sporadic.Co2.Native.co2Data) ≤ CFSG.Sporadic.Co2.Native.co2Data.orbSizes.prod := by
  obtain ⟨hfin, hcard⟩ := CFSG.Sporadic.Presentation.Co2.finite_card_le
  have hfin' : Finite TauCeti.Sporadic.co2Presentation.Group := hfin
  have hcard' : Nat.card TauCeti.Sporadic.co2Presentation.Group ≤ 42305421312000 := hcard
  exact card_le_of_rels _ gens (closure_ab _) KernelSpor.Co2Rels.relators (hcard'.trans (by decide))

theorem vecCert_co2 :
    vecCert CFSG.Sporadic.Co2.Native.co2Data 3 = true :=
  ok card_J_le

end CertificateChecks.KernelVec.Co2

end
