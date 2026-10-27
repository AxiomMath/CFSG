module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.ModelBlocksInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.RankThree.Native.ONTriplePresInputs

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMisc.ON

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37

theorem ptsQ72 : ptsOK (1023 * 72) 1023 = true := by quickRfl
theorem ptsQ73 : ptsOK (1023 * 73) 1023 = true := by quickRfl
theorem ptsQ74 : ptsOK (1023 * 74) 1023 = true := by quickRfl
theorem ptsQ75 : ptsOK (1023 * 75) 1023 = true := by quickRfl
theorem ptsQ76 : ptsOK (1023 * 76) 1023 = true := by quickRfl
theorem ptsQ77 : ptsOK (1023 * 77) 1023 = true := by quickRfl
theorem ptsQ78 : ptsOK (1023 * 78) 1023 = true := by quickRfl
theorem ptsQ79 : ptsOK (1023 * 79) 1023 = true := by quickRfl
theorem ptsQ80 : ptsOK (1023 * 80) 1023 = true := by quickRfl
theorem ptsQ81 : ptsOK (1023 * 81) 1023 = true := by quickRfl
theorem ptsQ82 : ptsOK (1023 * 82) 1023 = true := by quickRfl
theorem ptsQ83 : ptsOK (1023 * 83) 1023 = true := by quickRfl

theorem blk6 : ∀ q, 72 ≤ q → q < 84 → ptsOK (1023 * q) 1023 = true := by
  intro q h1 h2
  interval_cases q
  exacts [ptsQ72, ptsQ73, ptsQ74, ptsQ75, ptsQ76, ptsQ77, ptsQ78, ptsQ79, ptsQ80, ptsQ81, ptsQ82,
    ptsQ83]

end CertificateChecks.KernelMisc.ON

end
