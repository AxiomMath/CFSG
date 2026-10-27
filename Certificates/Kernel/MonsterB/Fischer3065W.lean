
module

public import Certificates.Kernel.MonsterB.Fischer3065T

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelMonB.F3065

theorem kW0 : (List.range' 0 13).all gramRowT = true := by decide +kernel
theorem kW1 : (List.range' 13 13).all gramRowT = true := by decide +kernel
theorem kW2 : (List.range' 26 13).all gramRowT = true := by decide +kernel
theorem kW3 : (List.range' 39 13).all gramRowT = true := by decide +kernel
theorem kW4 : (List.range' 52 13).all gramRowT = true := by decide +kernel
theorem kW5 : (List.range' 65 13).all gramRowT = true := by decide +kernel

end CertificateChecks.KernelMonB.F3065

end
