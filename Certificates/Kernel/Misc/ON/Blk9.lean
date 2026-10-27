module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.ModelBlocksInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.RankThree.Native.ONTriplePresInputs

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMisc.ON

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37

theorem ptsQ108 : ptsOK (1023 * 108) 1023 = true := by quickRfl
theorem ptsQ109 : ptsOK (1023 * 109) 1023 = true := by quickRfl
theorem ptsQ110 : ptsOK (1023 * 110) 1023 = true := by quickRfl
theorem ptsQ111 : ptsOK (1023 * 111) 1023 = true := by quickRfl
theorem ptsQ112 : ptsOK (1023 * 112) 1023 = true := by quickRfl
theorem ptsQ113 : ptsOK (1023 * 113) 1023 = true := by quickRfl
theorem ptsQ114 : ptsOK (1023 * 114) 1023 = true := by quickRfl
theorem ptsQ115 : ptsOK (1023 * 115) 1023 = true := by quickRfl
theorem ptsQ116 : ptsOK (1023 * 116) 1023 = true := by quickRfl
theorem ptsQ117 : ptsOK (1023 * 117) 1023 = true := by quickRfl
theorem ptsQ118 : ptsOK (1023 * 118) 1023 = true := by quickRfl
theorem ptsQ119 : ptsOK (1023 * 119) 1023 = true := by quickRfl

theorem blk9 : ∀ q, 108 ≤ q → q < 120 → ptsOK (1023 * q) 1023 = true := by
  intro q h1 h2
  interval_cases q
  exacts [ptsQ108, ptsQ109, ptsQ110, ptsQ111, ptsQ112, ptsQ113, ptsQ114, ptsQ115, ptsQ116, ptsQ117,
    ptsQ118, ptsQ119]

end CertificateChecks.KernelMisc.ON

end
