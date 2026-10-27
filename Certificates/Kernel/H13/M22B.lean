module

public import Certificates.Kernel.H13.M22Tac

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.M22Cert

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem m22_e0B_true : e0B = true := by m22_tac

set_option maxHeartbeats 0 in
theorem m22_witB_true : witB = true := by m22_tac

set_option maxHeartbeats 0 in
theorem m22_oB_true : oB = true := by m22_tac

set_option maxHeartbeats 0 in
theorem m22_m12B_true : m12B = true := by m22_tac

end CertificateChecks.KernelH13

end
