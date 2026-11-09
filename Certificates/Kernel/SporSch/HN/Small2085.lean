module

public import CFSG.Sporadic.HNOddCore.FiveCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic

public section

namespace CertificateChecks.KernelSporSch.HNSmall2085

open CFSG.Sporadic.HNOddCore.Native CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier
  CFSG.Sporadic.HNSchreier.Native CFSG.Sporadic.F5.Native CFSG.Sporadic.Th.Native CFSG.Certificates.Native

set_option Elab.async false

set_option maxRecDepth 100000 in
theorem small_1 :
    natChainOK (extendStrong 12 #[natArr LocalData.natGen1, natArr LocalData.natGen2] LocalData.strongWords) = true := by
  quickRfl

set_option maxRecDepth 100000 in
theorem small_2 :
    a6NatOK (extendStrong 12 #[natArr LocalData.natGen1, natArr LocalData.natGen2] LocalData.strongWords) = true := by
  quickRfl

set_option maxRecDepth 100000 in
theorem small_3 :
    iOrbitOK = true := by
  quickRfl

set_option maxRecDepth 100000 in
theorem small_4 :
    aOrbitsOK = true := by
  quickRfl

set_option maxRecDepth 100000 in
theorem small_5 :
    labelsOK (extendStrong 12 #[natArr LocalData.natGen1, natArr LocalData.natGen2] LocalData.strongWords) = true := by
  quickRfl

set_option maxRecDepth 100000 in
theorem small_6 :
    gammaOK orb7 orb42 = true := by
  quickRfl

set_option maxRecDepth 100000 in
theorem small_7 :
    fiberOK = true := by
  quickRfl

set_option maxRecDepth 100000 in
theorem small_8 :
    pairsOK = true := by
  quickRfl

theorem small : fiveSmallChecks = true := by
  unfold fiveSmallChecks fiveSmallChecksN
  rw [small_1, small_2, small_3, small_4, small_5, small_6, small_7, small_8]
  all_goals rfl

end CertificateChecks.KernelSporSch.HNSmall2085
