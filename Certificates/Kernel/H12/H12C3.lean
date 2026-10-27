module

public import Certificates.Kernel.H12.H12Tac
public import Certificates.Data.Kernel.H12C

public section

namespace CertificateChecks.KernelH12

open CFSG.Quasithin.H13.MatNCert CFSG.Quasithin.H.Mathieu.H12Cert CFSG.KC.H12C

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem h12_schC_true : schC = true := by
  simp only [schC, schE, inRT, inT, orbK, sA]
  h12_tac

end CertificateChecks.KernelH12

end
