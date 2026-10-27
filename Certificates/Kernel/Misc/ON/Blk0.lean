module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.ModelBlocksInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.RankThree.Native.ONTriplePresInputs

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMisc.ON

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37

theorem ptsQ0 : ptsOK (1023 * 0) 1023 = true := by quickRfl
theorem ptsQ1 : ptsOK (1023 * 1) 1023 = true := by quickRfl
theorem ptsQ2 : ptsOK (1023 * 2) 1023 = true := by quickRfl
theorem ptsQ3 : ptsOK (1023 * 3) 1023 = true := by quickRfl
theorem ptsQ4 : ptsOK (1023 * 4) 1023 = true := by quickRfl
theorem ptsQ5 : ptsOK (1023 * 5) 1023 = true := by quickRfl
theorem ptsQ6 : ptsOK (1023 * 6) 1023 = true := by quickRfl
theorem ptsQ7 : ptsOK (1023 * 7) 1023 = true := by quickRfl
theorem ptsQ8 : ptsOK (1023 * 8) 1023 = true := by quickRfl
theorem ptsQ9 : ptsOK (1023 * 9) 1023 = true := by quickRfl
theorem ptsQ10 : ptsOK (1023 * 10) 1023 = true := by quickRfl
theorem ptsQ11 : ptsOK (1023 * 11) 1023 = true := by quickRfl

theorem blk0 : ∀ q < 12, ptsOK (1023 * q) 1023 = true := by
  intro q h
  interval_cases q
  exacts [ptsQ0, ptsQ1, ptsQ2, ptsQ3, ptsQ4, ptsQ5, ptsQ6, ptsQ7, ptsQ8, ptsQ9, ptsQ10, ptsQ11]

end CertificateChecks.KernelMisc.ON

end
