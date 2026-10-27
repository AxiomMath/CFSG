
module

public import Certificates.Kernel.MonsterB.Fischer3067T

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelMonB.F3067

theorem kLC : lcChk = true := by decide +kernel

theorem kInv0 : invChk 0 = true := by decide +kernel
theorem kInv1 : invChk 1 = true := by decide +kernel
theorem kInv2 : invChk 2 = true := by decide +kernel
theorem kInv3 : invChk 3 = true := by decide +kernel
theorem kInv4 : invChk 4 = true := by decide +kernel
theorem kInv5 : invChk 5 = true := by decide +kernel
theorem kInv6 : invChk 6 = true := by decide +kernel
theorem kInv7 : invChk 7 = true := by decide +kernel
theorem kInv8 : invChk 8 = true := by decide +kernel
theorem kInv9 : invChk 9 = true := by decide +kernel
theorem kInv10 : invChk 10 = true := by decide +kernel
theorem kInv11 : invChk 11 = true := by decide +kernel
theorem kInv12 : invChk 12 = true := by decide +kernel

end CertificateChecks.KernelMonB.F3067

end
