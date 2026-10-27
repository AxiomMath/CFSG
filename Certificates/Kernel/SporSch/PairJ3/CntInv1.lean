module

public import Certificates.Kernel.SporSch.PairJ3.CntInv0
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_b2 CertificateChecks.KernelSporSch.PJ3Cn CertificateChecks.KernelSporSch.PJ3Cn.invB 7 13 4
#kss_b2all CertificateChecks.KernelSporSch.PJ3Cn CertificateChecks.KernelSporSch.PJ3Cn.invB 13 4

end
