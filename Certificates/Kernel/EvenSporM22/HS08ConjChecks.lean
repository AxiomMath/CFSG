module

public import Certificates.Data.Kernel.EvenSporM22.HS08ConjDefs

public section

namespace CertificateChecks.KernelEvenSporM22

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.HS08Check
  CFSG.KC.EvenSporM22

theorem hs08cPairs_length : cPairs.length = 231 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hs08cPairs_ok : HS08PairsOK cPairs := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hs08jLit_valid : ∀ x ∈ jLit, hs08TabV x = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hs08keys_ok : hs08KeysOK jLit cPairs = true := by
  decide +kernel

end CertificateChecks.KernelEvenSporM22
