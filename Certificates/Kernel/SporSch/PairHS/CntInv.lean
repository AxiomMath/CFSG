module

public import Certificates.Kernel.SporSch.PairHS.CntFns
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_b2 CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.invA 0 3 4
#kss_b2all CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.invA 3 4
#kss_b2 CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.invB 0 8 4
#kss_b2all CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.invB 8 4

end
