module

public import Certificates.Kernel.SporSch.PairJ3.CntFns
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.SporSch.PairClTSound
public import CFSG.Certificates.Kernel.SporSch.PairKSound

public section

set_option maxRecDepth 400000

#kss_b2 CertificateChecks.KernelSporSch.PJ3Cn CertificateChecks.KernelSporSch.PJ3Cn.scZ2 0 13 4
#kss_b2all CertificateChecks.KernelSporSch.PJ3Cn CertificateChecks.KernelSporSch.PJ3Cn.scZ2 13 4

end
