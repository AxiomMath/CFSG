module

public import Certificates.Kernel.MonsterB.Fischer3067T

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelMonB.F3067

theorem kE0 : (List.range' 0 256).all orbitEntryT = true := by decide +kernel
theorem kE1 : (List.range' 256 256).all orbitEntryT = true := by decide +kernel
theorem kE2 : (List.range' 512 256).all orbitEntryT = true := by decide +kernel
theorem kE3 : (List.range' 768 256).all orbitEntryT = true := by decide +kernel

end CertificateChecks.KernelMonB.F3067

end
