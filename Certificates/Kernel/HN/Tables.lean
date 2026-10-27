module

public import Certificates.Kernel.HN.Data
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.HN.T3vK000
import CFSG.Certificates.Kernel.Bounds.HN.T4vK000

public section

namespace CertificateChecks.KernelBounds.HN

theorem t3 : CFSG.KC.HNA.N5A.T3.ok = true := by kb_assemble HN_T3v
theorem t4 : CFSG.KC.HNA.N5A.T4.ok = true := by kb_assemble HN_T4v

end CertificateChecks.KernelBounds.HN

end
