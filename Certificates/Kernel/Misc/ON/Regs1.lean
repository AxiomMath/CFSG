module

public import CFSG.RankThree.Native.ONTripleModelInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.RankThree.Native.ONTriplePresInputs

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMisc.ON

open CFSG.RankThree.Native.ONTriple

theorem regs1 : ∀ r, 32 ≤ r → r < 56 → chkRegM r = true := by
  intro r h1 h2
  interval_cases r <;> quickRfl

end CertificateChecks.KernelMisc.ON

end
