module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.ModelBlocksInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.RankThree.Native.ONTriplePresInputs

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMisc.ON

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37 CFSG.KC.Misc.F7

theorem lrB : ∀ s < 16, lrOK s = true := by
  intro s h
  interval_cases s <;> quickRfl

theorem fixWB : ∀ l < 6, fixesOK 0 l = true := by
  intro l h
  interval_cases l <;> quickRfl

theorem orbFixB : ∀ o < 5, orbFixOK o = true := by
  intro o h
  interval_cases o <;> quickRfl

theorem zScalarB : zScalar = true := by quickRfl

theorem detB : ∀ k < 6, detOK k = true := by
  intro k h
  interval_cases k <;> quickRfl

end CertificateChecks.KernelMisc.ON

end
