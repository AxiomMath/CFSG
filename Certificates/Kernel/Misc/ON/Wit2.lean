module

public import CFSG.RankThree.Native.ONTripleLocalCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.RankThree.Native.ONTriplePresInputs

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMisc.ON

open CFSG.RankThree.Native.ONTriple

theorem wits2 : ∀ q, 6 ≤ q → q < 9 → chkWitM (9 * q) 9 = true := by
  intro q h1 h2
  interval_cases q <;> quickRfl

end CertificateChecks.KernelMisc.ON

end
