module

public import Certificates.Kernel.H13.M22OvDefs

public section

namespace CertificateChecks.KernelH13

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem m22_ov4_true : m22ov4 = true := by
  unfold m22ov4 m22ovU
  m22_tac

end CertificateChecks.KernelH13

end
