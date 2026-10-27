module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.ModelBlocksInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.RankThree.Native.ONTriplePresInputs

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMisc.ON

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37

theorem ptsQ60 : ptsOK (1023 * 60) 1023 = true := by quickRfl
theorem ptsQ61 : ptsOK (1023 * 61) 1023 = true := by quickRfl
theorem ptsQ62 : ptsOK (1023 * 62) 1023 = true := by quickRfl
theorem ptsQ63 : ptsOK (1023 * 63) 1023 = true := by quickRfl
theorem ptsQ64 : ptsOK (1023 * 64) 1023 = true := by quickRfl
theorem ptsQ65 : ptsOK (1023 * 65) 1023 = true := by quickRfl
theorem ptsQ66 : ptsOK (1023 * 66) 1023 = true := by quickRfl
theorem ptsQ67 : ptsOK (1023 * 67) 1023 = true := by quickRfl
theorem ptsQ68 : ptsOK (1023 * 68) 1023 = true := by quickRfl
theorem ptsQ69 : ptsOK (1023 * 69) 1023 = true := by quickRfl
theorem ptsQ70 : ptsOK (1023 * 70) 1023 = true := by quickRfl
theorem ptsQ71 : ptsOK (1023 * 71) 1023 = true := by quickRfl

theorem blk5 : ∀ q, 60 ≤ q → q < 72 → ptsOK (1023 * q) 1023 = true := by
  intro q h1 h2
  interval_cases q
  exacts [ptsQ60, ptsQ61, ptsQ62, ptsQ63, ptsQ64, ptsQ65, ptsQ66, ptsQ67, ptsQ68, ptsQ69, ptsQ70,
    ptsQ71]

end CertificateChecks.KernelMisc.ON

end
