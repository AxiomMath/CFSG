module

public import Certificates.Kernel.H12.H12Tac
public import Certificates.Data.Kernel.H12N

public section

namespace CertificateChecks.KernelH12

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem h12_ov4N_true : CFSG.KC.H12N.ov4N = true := by
  simp only [CFSG.KC.H12N.ov4N, CFSG.KC.H12N.ovU, CFSG.KC.H12N.ovY, CFSG.KC.H12N.lines4,
    CFSG.KC.H12N.ballV]
  h12_tac

end CertificateChecks.KernelH12

end
