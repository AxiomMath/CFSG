module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.ModelBlocksInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.RankThree.Native.ONTriplePresInputs

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMisc.ON

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37

theorem ptsQ96 : ptsOK (1023 * 96) 1023 = true := by quickRfl
theorem ptsQ97 : ptsOK (1023 * 97) 1023 = true := by quickRfl
theorem ptsQ98 : ptsOK (1023 * 98) 1023 = true := by quickRfl
theorem ptsQ99 : ptsOK (1023 * 99) 1023 = true := by quickRfl
theorem ptsQ100 : ptsOK (1023 * 100) 1023 = true := by quickRfl
theorem ptsQ101 : ptsOK (1023 * 101) 1023 = true := by quickRfl
theorem ptsQ102 : ptsOK (1023 * 102) 1023 = true := by quickRfl
theorem ptsQ103 : ptsOK (1023 * 103) 1023 = true := by quickRfl
theorem ptsQ104 : ptsOK (1023 * 104) 1023 = true := by quickRfl
theorem ptsQ105 : ptsOK (1023 * 105) 1023 = true := by quickRfl
theorem ptsQ106 : ptsOK (1023 * 106) 1023 = true := by quickRfl
theorem ptsQ107 : ptsOK (1023 * 107) 1023 = true := by quickRfl

theorem blk8 : ∀ q, 96 ≤ q → q < 108 → ptsOK (1023 * q) 1023 = true := by
  intro q h1 h2
  interval_cases q
  exacts [ptsQ96, ptsQ97, ptsQ98, ptsQ99, ptsQ100, ptsQ101, ptsQ102, ptsQ103, ptsQ104, ptsQ105,
    ptsQ106, ptsQ107]

end CertificateChecks.KernelMisc.ON

end
