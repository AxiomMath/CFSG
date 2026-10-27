module

public import Certificates.Kernel.J1Syl.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ1Syl

theorem shape_ok : shapeOK = true := by decide +kernel
theorem keysOK_ok : keysOK = true := by quickRfl
theorem vKeys_ok : vKeysOK = true := by quickRfl
theorem fNe_ok : fNe = true := by quickRfl
theorem b_ok : bOK = true := by quickRfl

end CertificateChecks.KernelJ1Syl

end
