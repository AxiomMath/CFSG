module

public import Certificates.Kernel.MonsterB.Fischer3067T

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelMonB.F3067

theorem kE4 : (List.range' 1024 256).all orbitEntryT = true := by decide +kernel
theorem kE5 : (List.range' 1280 256).all orbitEntryT = true := by decide +kernel
theorem kE6 : (List.range' 1536 256).all orbitEntryT = true := by decide +kernel
theorem kE7 : (List.range' 1792 256).all orbitEntryT = true := by decide +kernel

end CertificateChecks.KernelMonB.F3067

end
