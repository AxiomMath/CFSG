module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3SevenModelInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.RankThree.Native.ONTriplePresInputs
public import CFSG.RankThree.Native.ONTripleSigCheckInputs
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3SevenRels

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMisc.ON

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven

theorem l37Rel0 : ∀ q < 2, chkRelM 0 q = true := by
  intro q hq
  interval_cases q <;> quickRfl

end CertificateChecks.KernelMisc.ON

end
