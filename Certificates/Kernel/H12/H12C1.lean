module

public import Certificates.Kernel.H12.H12Tac
public import Certificates.Data.Kernel.H12C

public section

namespace CertificateChecks.KernelH12

open CFSG.Quasithin.H13.MatNCert CFSG.Quasithin.H.Mathieu.H12Cert CFSG.KC.H12C

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem h12_zB_true : zB = true := by h12_tac

set_option maxHeartbeats 0 in
theorem h12_orbB_true : orbB = true := by h12_tac

set_option maxHeartbeats 0 in
theorem h12_wB_true : wB = true := by
  simp only [wB]
  h12_tac

set_option maxHeartbeats 0 in
theorem h12_tB2_true : tB2 = true := by
  simp only [tB2]
  h12_tac

set_option maxHeartbeats 0 in
theorem h12_cosS_true : cosB s0G rP sA 1360 = true := by
  simp only [cosB, inT, sA]
  h12_tac

end CertificateChecks.KernelH12

end
