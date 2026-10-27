module

public import CFSG.LocalAnalysis.StandardType.TitsThreeOvergroupData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOver.Three

open CFSG.StandardType.TitsThree

theorem k_rlen : Nat.beq pairData.repW.length 456 = true := by quickRfl
theorem k_klen : Nat.beq pairData.kind.length 456 = true := by quickRfl
theorem k_glen : Nat.beq pairData.genW.length 456 = true := by quickRfl

end CertificateChecks.KernelTitsOver.Three

end
