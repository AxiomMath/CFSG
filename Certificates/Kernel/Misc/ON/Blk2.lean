module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.ModelBlocksInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.RankThree.Native.ONTriplePresInputs

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMisc.ON

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37

theorem ptsQ24 : ptsOK (1023 * 24) 1023 = true := by quickRfl
theorem ptsQ25 : ptsOK (1023 * 25) 1023 = true := by quickRfl
theorem ptsQ26 : ptsOK (1023 * 26) 1023 = true := by quickRfl
theorem ptsQ27 : ptsOK (1023 * 27) 1023 = true := by quickRfl
theorem ptsQ28 : ptsOK (1023 * 28) 1023 = true := by quickRfl
theorem ptsQ29 : ptsOK (1023 * 29) 1023 = true := by quickRfl
theorem ptsQ30 : ptsOK (1023 * 30) 1023 = true := by quickRfl
theorem ptsQ31 : ptsOK (1023 * 31) 1023 = true := by quickRfl
theorem ptsQ32 : ptsOK (1023 * 32) 1023 = true := by quickRfl
theorem ptsQ33 : ptsOK (1023 * 33) 1023 = true := by quickRfl
theorem ptsQ34 : ptsOK (1023 * 34) 1023 = true := by quickRfl
theorem ptsQ35 : ptsOK (1023 * 35) 1023 = true := by quickRfl

theorem blk2 : ∀ q, 24 ≤ q → q < 36 → ptsOK (1023 * q) 1023 = true := by
  intro q h1 h2
  interval_cases q
  exacts [ptsQ24, ptsQ25, ptsQ26, ptsQ27, ptsQ28, ptsQ29, ptsQ30, ptsQ31, ptsQ32, ptsQ33, ptsQ34,
    ptsQ35]

end CertificateChecks.KernelMisc.ON

end
