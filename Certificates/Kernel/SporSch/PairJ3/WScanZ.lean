module

public import Certificates.Kernel.SporSch.PairJ3.WScanFns
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.SporSch.PairClTSound
public import CFSG.Certificates.Kernel.SporSch.PairKSound

public section

set_option maxRecDepth 400000

#kss_b2 CertificateChecks.KernelSporSch.PJ3W CertificateChecks.KernelSporSch.PJ3W.scW 0 13 4
#kss_b2all CertificateChecks.KernelSporSch.PJ3W CertificateChecks.KernelSporSch.PJ3W.scW 13 4

end
