module

public import Certificates.Data.Kernel.PermCent.M22BTwin

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelPermCent

open CFSG.LocalAnalysis.GLTheoremA.KD1426M22 CFSG.Certificates.Kernel.PkCV

theorem k10140 : M22B.kleinC = true := by decide +kernel

end CertificateChecks.KernelPermCent
