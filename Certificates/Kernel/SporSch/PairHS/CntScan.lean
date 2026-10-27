module

public import Certificates.Kernel.SporSch.PairHS.CntFns
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_b2 CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.scA 0 3 4
#kss_b2all CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.scA 3 4
#kss_b2 CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.scAI 0 3 4
#kss_b2all CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.scAI 3 4
#kss_b2 CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.scB 0 8 4
#kss_b2all CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.scB 8 4
#kss_b2 CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.scBI 0 8 4
#kss_b2all CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.scBI 8 4

end
