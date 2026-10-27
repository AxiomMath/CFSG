module

public import CFSG.Sporadic.HNOddCore.FiveCheckInputs
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic

public section

namespace CertificateChecks.KernelSporSch.HNSmall2085

open CFSG.Sporadic.HNOddCore.Native

set_option maxRecDepth 100000 in
theorem small : fiveSmallChecks = true := by
  decide +kernel

end CertificateChecks.KernelSporSch.HNSmall2085
