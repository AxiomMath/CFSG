module

public import CFSG.RankThree.Native.ONTripleSigCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.RankThree.Native.ONTriplePresInputs

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMisc.ON

open CFSG.RankThree.Native.ONTriple

theorem chkLMB : chkLM = true := by quickRfl

theorem chkVx0MB : chkVx0M = true := by quickRfl

theorem chkYMB : chkYM = true := by quickRfl

theorem chkX12MB : chkX12M = true := by quickRfl

end CertificateChecks.KernelMisc.ON

end
