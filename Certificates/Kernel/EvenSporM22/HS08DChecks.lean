module

public import Certificates.Data.Kernel.EvenSporM22.HS08DDefs

public section

namespace CertificateChecks.KernelEvenSporM22

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.HS08Check
  CFSG.KC.EvenSporM22

theorem hs08dGens_valid : ∀ g ∈ dGens, hs08TabV g = true := by
  decide +kernel

theorem hs08dReps_valid : ∀ r ∈ dReps, hs08TabV r = true := by
  decide +kernel

theorem hs08dLens : dReps.length = 15 ∧ dGens.length = 9 ∧ dTabs.length = 3840 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hs08dRecs_ok : HS08DRecOK hs08DRecs := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hs08dKeys_ok : CFSG.Decide.bitsetNodup (dTabs.map hs08DKey) = true := by
  decide +kernel

theorem hs08dId : idTab ∈ dTabs := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hs08dNorm_jLit : ∀ g ∈ dGens, ∀ j ∈ jLit, ∃ j' ∈ jLit, tmul g j = tmul j' g := by
  decide +kernel

end CertificateChecks.KernelEvenSporM22
