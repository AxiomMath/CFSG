module

public import Certificates.Kernel.SporSch.PairHS.HS7208Fns
public import Certificates.Kernel.SporSch.PairJ3.GenClT
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_b2 CertificateChecks.KernelSporSch.HS78 CertificateChecks.KernelSporSch.HS78.eB 0 8 8
#kss_b2all CertificateChecks.KernelSporSch.HS78 CertificateChecks.KernelSporSch.HS78.eB 8 8

end
