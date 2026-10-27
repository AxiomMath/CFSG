module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.ModelBlocksInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.RankThree.Native.ONTriplePresInputs

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMisc.ON

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37

theorem ptsQ84 : ptsOK (1023 * 84) 1023 = true := by quickRfl
theorem ptsQ85 : ptsOK (1023 * 85) 1023 = true := by quickRfl
theorem ptsQ86 : ptsOK (1023 * 86) 1023 = true := by quickRfl
theorem ptsQ87 : ptsOK (1023 * 87) 1023 = true := by quickRfl
theorem ptsQ88 : ptsOK (1023 * 88) 1023 = true := by quickRfl
theorem ptsQ89 : ptsOK (1023 * 89) 1023 = true := by quickRfl
theorem ptsQ90 : ptsOK (1023 * 90) 1023 = true := by quickRfl
theorem ptsQ91 : ptsOK (1023 * 91) 1023 = true := by quickRfl
theorem ptsQ92 : ptsOK (1023 * 92) 1023 = true := by quickRfl
theorem ptsQ93 : ptsOK (1023 * 93) 1023 = true := by quickRfl
theorem ptsQ94 : ptsOK (1023 * 94) 1023 = true := by quickRfl
theorem ptsQ95 : ptsOK (1023 * 95) 1023 = true := by quickRfl

theorem blk7 : ∀ q, 84 ≤ q → q < 96 → ptsOK (1023 * q) 1023 = true := by
  intro q h1 h2
  interval_cases q
  exacts [ptsQ84, ptsQ85, ptsQ86, ptsQ87, ptsQ88, ptsQ89, ptsQ90, ptsQ91, ptsQ92, ptsQ93, ptsQ94,
    ptsQ95]

end CertificateChecks.KernelMisc.ON

end
