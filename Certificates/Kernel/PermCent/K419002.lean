module

public import Certificates.Data.Kernel.PermCent.M11BTwin

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelPermCent

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.M11B

theorem k419002_cent : centC = true := by decide +kernel

theorem k419002_cent18 : cent18C = true := by decide +kernel

theorem k419002_move : moveC = true := by decide +kernel

end CertificateChecks.KernelPermCent
