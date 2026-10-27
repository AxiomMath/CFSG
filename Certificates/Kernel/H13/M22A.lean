module

public import Certificates.Kernel.H13.M22Tac

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.M22Cert

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem m22_orbB_true : orbB = true := by m22_tac

set_option maxHeartbeats 0 in
theorem m22_s0B_true : s0B = true := by m22_tac

set_option maxHeartbeats 0 in
theorem m22_schB_true : schB = true := by m22_tac

set_option maxHeartbeats 0 in
theorem m22_pB_true : pB = true := by m22_tac

end CertificateChecks.KernelH13

end
