module

public import Certificates.Kernel.MonsterB.Fischer3067B
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelMonB.F3067

theorem kOrb : orbChkB orbitDataB = true := by decide +kernel

end CertificateChecks.KernelMonB.F3067

end
