module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.ModelBlocksInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.RankThree.Native.ONTriplePresInputs

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMisc.ON

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37

theorem ptsQ48 : ptsOK (1023 * 48) 1023 = true := by quickRfl
theorem ptsQ49 : ptsOK (1023 * 49) 1023 = true := by quickRfl
theorem ptsQ50 : ptsOK (1023 * 50) 1023 = true := by quickRfl
theorem ptsQ51 : ptsOK (1023 * 51) 1023 = true := by quickRfl
theorem ptsQ52 : ptsOK (1023 * 52) 1023 = true := by quickRfl
theorem ptsQ53 : ptsOK (1023 * 53) 1023 = true := by quickRfl
theorem ptsQ54 : ptsOK (1023 * 54) 1023 = true := by quickRfl
theorem ptsQ55 : ptsOK (1023 * 55) 1023 = true := by quickRfl
theorem ptsQ56 : ptsOK (1023 * 56) 1023 = true := by quickRfl
theorem ptsQ57 : ptsOK (1023 * 57) 1023 = true := by quickRfl
theorem ptsQ58 : ptsOK (1023 * 58) 1023 = true := by quickRfl
theorem ptsQ59 : ptsOK (1023 * 59) 1023 = true := by quickRfl

theorem blk4 : ∀ q, 48 ≤ q → q < 60 → ptsOK (1023 * q) 1023 = true := by
  intro q h1 h2
  interval_cases q
  exacts [ptsQ48, ptsQ49, ptsQ50, ptsQ51, ptsQ52, ptsQ53, ptsQ54, ptsQ55, ptsQ56, ptsQ57, ptsQ58,
    ptsQ59]

end CertificateChecks.KernelMisc.ON

end
