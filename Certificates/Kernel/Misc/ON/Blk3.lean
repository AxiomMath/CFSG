module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.ModelBlocksInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.RankThree.Native.ONTriplePresInputs

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMisc.ON

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37

theorem ptsQ36 : ptsOK (1023 * 36) 1023 = true := by quickRfl
theorem ptsQ37 : ptsOK (1023 * 37) 1023 = true := by quickRfl
theorem ptsQ38 : ptsOK (1023 * 38) 1023 = true := by quickRfl
theorem ptsQ39 : ptsOK (1023 * 39) 1023 = true := by quickRfl
theorem ptsQ40 : ptsOK (1023 * 40) 1023 = true := by quickRfl
theorem ptsQ41 : ptsOK (1023 * 41) 1023 = true := by quickRfl
theorem ptsQ42 : ptsOK (1023 * 42) 1023 = true := by quickRfl
theorem ptsQ43 : ptsOK (1023 * 43) 1023 = true := by quickRfl
theorem ptsQ44 : ptsOK (1023 * 44) 1023 = true := by quickRfl
theorem ptsQ45 : ptsOK (1023 * 45) 1023 = true := by quickRfl
theorem ptsQ46 : ptsOK (1023 * 46) 1023 = true := by quickRfl
theorem ptsQ47 : ptsOK (1023 * 47) 1023 = true := by quickRfl

theorem blk3 : ∀ q, 36 ≤ q → q < 48 → ptsOK (1023 * q) 1023 = true := by
  intro q h1 h2
  interval_cases q
  exacts [ptsQ36, ptsQ37, ptsQ38, ptsQ39, ptsQ40, ptsQ41, ptsQ42, ptsQ43, ptsQ44, ptsQ45, ptsQ46,
    ptsQ47]

end CertificateChecks.KernelMisc.ON

end
