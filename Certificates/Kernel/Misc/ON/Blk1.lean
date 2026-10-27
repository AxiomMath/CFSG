module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.ModelBlocksInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.RankThree.Native.ONTriplePresInputs

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMisc.ON

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37

theorem ptsQ12 : ptsOK (1023 * 12) 1023 = true := by quickRfl
theorem ptsQ13 : ptsOK (1023 * 13) 1023 = true := by quickRfl
theorem ptsQ14 : ptsOK (1023 * 14) 1023 = true := by quickRfl
theorem ptsQ15 : ptsOK (1023 * 15) 1023 = true := by quickRfl
theorem ptsQ16 : ptsOK (1023 * 16) 1023 = true := by quickRfl
theorem ptsQ17 : ptsOK (1023 * 17) 1023 = true := by quickRfl
theorem ptsQ18 : ptsOK (1023 * 18) 1023 = true := by quickRfl
theorem ptsQ19 : ptsOK (1023 * 19) 1023 = true := by quickRfl
theorem ptsQ20 : ptsOK (1023 * 20) 1023 = true := by quickRfl
theorem ptsQ21 : ptsOK (1023 * 21) 1023 = true := by quickRfl
theorem ptsQ22 : ptsOK (1023 * 22) 1023 = true := by quickRfl
theorem ptsQ23 : ptsOK (1023 * 23) 1023 = true := by quickRfl

theorem blk1 : ∀ q, 12 ≤ q → q < 24 → ptsOK (1023 * q) 1023 = true := by
  intro q h1 h2
  interval_cases q
  exacts [ptsQ12, ptsQ13, ptsQ14, ptsQ15, ptsQ16, ptsQ17, ptsQ18, ptsQ19, ptsQ20, ptsQ21, ptsQ22,
    ptsQ23]

end CertificateChecks.KernelMisc.ON

end
