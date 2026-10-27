module

public import Certificates.Kernel.VecCert.HS
public import Certificates.Kernel.VecCert.Bound
public import Certificates.Kernel.Sporadic.HS.Rels
public import CFSG.Sporadic.Presentation.HSExact
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Sporadic.Presentation.Common

public section

namespace CertificateChecks.KernelVec.HS

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

theorem gens : TauCeti.Sporadic.hsPresentation.generatorCount = 2 := by
  simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.hsPresentation_generatorNames]

theorem card_J_le :
    Nat.card (J CFSG.Sporadic.HS.Native.hsData) ≤ CFSG.Sporadic.HS.Native.hsData.orbSizes.prod := by
  obtain ⟨hfin, hcard⟩ := CFSG.Sporadic.Presentation.HS.finite_card_le
  have hfin' : Finite TauCeti.Sporadic.hsPresentation.Group := hfin
  have hcard' : Nat.card TauCeti.Sporadic.hsPresentation.Group ≤ 44352000 := hcard
  exact card_le_of_rels _ gens (closure_ab _) KernelSpor.HSRels.relators (hcard'.trans (by decide))

theorem vecCert_hs :
    vecCert CFSG.Sporadic.HS.Native.hsData 3 = true :=
  ok card_J_le

end CertificateChecks.KernelVec.HS

end
