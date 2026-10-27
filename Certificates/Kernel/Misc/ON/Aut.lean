module

public import CFSG.RankThree.Native.ONTripleAutCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.RankThree.Native.ONTriplePresInputs

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMisc.ON

open CFSG.RankThree.Native.ONTriple

theorem autRegsB : ∀ r, 9 ≤ r → r < 24 → chkAutRegM r = true := by
  intro r h1 h2
  interval_cases r <;> quickRfl

theorem chkGenMB : chkGenM = true := by quickRfl

theorem chkT4MB : chkT4M = true := by quickRfl

theorem chkCMB : chkCM = true := by quickRfl

end CertificateChecks.KernelMisc.ON

end
