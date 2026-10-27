module

public import Certificates.Kernel.H12.H12Tac
public import Certificates.Data.Kernel.H12C

public section

namespace CertificateChecks.KernelH12

open CFSG.Quasithin.H13.MatNCert CFSG.Quasithin.H.Mathieu.H12Cert CFSG.KC.H12C

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem h12_cosR_true : cosB rG r0P [5] 5 = true := by
  simp only [cosB, inT]
  h12_tac

set_option maxHeartbeats 0 in
theorem h12_ov1C_true : ov1C = true := by
  simp only [ov1C, ball3]
  h12_tac

end CertificateChecks.KernelH12

end
