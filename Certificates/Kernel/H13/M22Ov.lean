module

public import Certificates.Kernel.H13.M22OvDefs

public section

namespace CertificateChecks.KernelH13

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem m22_ov1_true : m22ov1 = true := by
  unfold m22ov1
  m22_tac

set_option maxHeartbeats 0 in
theorem m22_ov2_true : m22ov2 = true := by
  unfold m22ov2
  m22_tac

set_option maxHeartbeats 0 in
theorem m22_ov3_true : m22ov3 = true := by
  unfold m22ov3
  m22_tac

set_option maxHeartbeats 0 in
theorem m22_ov5_true : m22ov5 = true := by
  unfold m22ov5
  m22_tac

end CertificateChecks.KernelH13

end
