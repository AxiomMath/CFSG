module

public import Certificates.Kernel.Ly.Data
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.Ly.T2vK000
import CFSG.Certificates.Kernel.Bounds.Ly.T3vK000
import CFSG.Certificates.Kernel.Bounds.Ly.T4vK000

public section

namespace CertificateChecks.KernelBounds.Ly

theorem t2 : CFSG.KC.LyA.G25.T2.ok = true := by kb_assemble Ly_T2v
theorem t3 : CFSG.KC.LyA.G25.T3.ok = true := by kb_assemble Ly_T3v
theorem t4 : CFSG.KC.LyA.G25.T4.ok = true := by kb_assemble Ly_T4v

end CertificateChecks.KernelBounds.Ly

end
