module

public import Certificates.Data.Kernel.EvenSporM22.HS08NDefs

public section

namespace CertificateChecks.KernelEvenSporM22

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.OutCheck
  CFSG.EvenSporadicStandard.M22Std.HS08Check CFSG.KC.EvenSporM22

theorem hs08nLens : (jInnJ jLit).length = 16 ∧ (jOutJ jLit).length = 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hs08nCent : HS08CentOK hs08CentT := by
  decide +kernel

theorem hs08nW4 :
    HS08WitOK (x4J jLit) ((jInnJ jLit).filter fun l => decide (l ≠ idTab)) hs08W4 := by
  decide +kernel

theorem hs08nW6 : HS08WitOK (x6J jLit) hs08O6 hs08W6 := by
  decide +kernel

theorem hs08nW10 : HS08WitOK (x10J jLit) hs08O10 hs08W10 := by
  decide +kernel

theorem hs08nMem : x4J jLit ∈ jLit ∧ x6J jLit ∈ jLit ∧ x10J jLit ∈ jLit := by
  decide +kernel

theorem hs08nOrbs :
    (jOutJ jLit).filter (fun y => decide (y ∈ hs08O6)) = hs08O6 ∧
    (jOutJ jLit).filter (fun y => decide (y ∈ hs08O10)) = hs08O10 ∧
    hs08O6.length = 6 ∧ hs08O10.length = 10 ∧
    (∀ y ∈ jOutJ jLit, y ∈ hs08O6 ∨ y ∈ hs08O10) ∧ (∀ y ∈ hs08O6, y ∉ hs08O10) ∧
    x6J jLit ∈ hs08O6 ∧ x10J jLit ∈ hs08O10 ∧ (∀ y ∈ hs08O6, hs08TabV y = true) ∧
    (∀ y ∈ hs08O10, hs08TabV y = true) ∧ ∀ y ∈ jOutJ jLit, hs08TabV y = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hs08nNorms : ∀ g ∈ s0Gens ++ dReps, HS08Norms hs08O6 g ∧ HS08Norms hs08O10 g := by
  decide +kernel

theorem hs08nInv : ∀ g ∈ s0Gens ++ dReps, hs08TabV (tinv g) = true ∧ tmul g (tinv g) = idTab := by
  decide +kernel

end CertificateChecks.KernelEvenSporM22
