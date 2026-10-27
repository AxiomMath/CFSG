module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.LSubAlphaInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.RankThree.Native.ONTriplePresInputs

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMisc.ON

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37 CFSG.KC.Misc.F7
open CFSG.RankThree.Native.ONTriple

theorem alphaB : ∀ k < 9, alphaOK k = true := by
  intro k h
  interval_cases k <;> quickRfl

end CertificateChecks.KernelMisc.ON

end
