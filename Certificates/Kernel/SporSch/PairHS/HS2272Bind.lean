module

public import Certificates.Kernel.SporSch.PairHS.HS2272Fns
public import Certificates.Kernel.SporSch.PairJ3.GenClT
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_b2 CertificateChecks.KernelSporSch.HS72 CertificateChecks.KernelSporSch.HS72.bindB 0 22 5
#kss_b2all CertificateChecks.KernelSporSch.HS72 CertificateChecks.KernelSporSch.HS72.bindB 22 5
#kss_b2 CertificateChecks.KernelSporSch.HS72 CertificateChecks.KernelSporSch.HS72.uaB 0 2 5
#kss_b2all CertificateChecks.KernelSporSch.HS72 CertificateChecks.KernelSporSch.HS72.uaB 2 5

end
