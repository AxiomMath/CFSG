module

public import Certificates.Kernel.SporSch.PairHS.ClFns
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_b2 CertificateChecks.KernelSporSch.PHSCl CertificateChecks.KernelSporSch.PHSCl.runA 0 23 8
#kss_b2all CertificateChecks.KernelSporSch.PHSCl CertificateChecks.KernelSporSch.PHSCl.runA 23 8

end
