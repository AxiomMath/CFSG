module

public import Certificates.Kernel.SporSch.PairJ3.OrbFns
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_b2 CertificateChecks.KernelSporSch.PJ3Cn CertificateChecks.KernelSporSch.PJ3Cn.orbB 0 3 8
#kss_b2all CertificateChecks.KernelSporSch.PJ3Cn CertificateChecks.KernelSporSch.PJ3Cn.orbB 3 8

#kss_b2 CertificateChecks.KernelSporSch.PJ3Cn CertificateChecks.KernelSporSch.PJ3Cn.permB 0 13 4
#kss_b2all CertificateChecks.KernelSporSch.PJ3Cn CertificateChecks.KernelSporSch.PJ3Cn.permB 13 4

namespace CertificateChecks.KernelSporSch.PJ3Cn

theorem rep_ok : repB = true := by quickRfl

theorem op_ok : opB = true := by quickRfl

theorem op2_ok : opB2 = true := by quickRfl

end CertificateChecks.KernelSporSch.PJ3Cn

end
