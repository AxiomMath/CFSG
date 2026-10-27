module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxPGData

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelTwoHSLe4.Chi

open CFSG.EvenSporadicStandard.TwoHS

theorem card_omega : Fintype.card OmegaPts = 600 := by decide +kernel
theorem fix_r0 : fixCount (toM (pgReflC 0)) = 0 := by decide +kernel
theorem fix_r1 : fixCount (toM (pgReflC 1)) = 2 := by decide +kernel
theorem fix_r2 : fixCount (toM (pgReflC 2)) = 0 := by decide +kernel
theorem fix_r3 : fixCount (toM (pgReflC 3)) = 2 := by decide +kernel
theorem fix_s1 : fixCount pgS1 = 30 := by decide +kernel
theorem fix_tau1 : fixCount pgTau1 = 20 := by decide +kernel

theorem chi : PGChiF :=
  ⟨card_omega, fix_r0, fix_r1, fix_r2, fix_r3, fix_s1, fix_tau1⟩

end CertificateChecks.KernelTwoHSLe4.Chi

end
