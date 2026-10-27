module

public import Certificates.Data.Kernel.PermCent.U33BTwin

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelPermCent

open CFSG.GH74.KGroups.U33 CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.U33B

theorem k295133_ord : noOrdC = true := by decide +kernel

theorem k295133_e8 : e8C = true := by decide +kernel

end CertificateChecks.KernelPermCent
