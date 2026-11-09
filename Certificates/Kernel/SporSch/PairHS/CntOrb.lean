module

public import Certificates.Kernel.SporSch.PairHS.OrbFns
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_b2 CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.orbA 0 2 8
#kss_b2all CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.orbA 2 8

#kss_b2 CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.orbB 0 3 8
#kss_b2all CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.orbB 3 8

#kss_b2 CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.permA 0 3 4
#kss_b2all CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.permA 3 4

#kss_b2 CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.permB 0 4 8
#kss_b2all CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.permB 4 8

namespace CertificateChecks.KernelSporSch.PHSCn

theorem rep_ok : repB = true := by quickRfl

theorem op_ok : opB = true := by quickRfl

theorem op2_ok : opB2 = true := by quickRfl

end CertificateChecks.KernelSporSch.PHSCn

end
