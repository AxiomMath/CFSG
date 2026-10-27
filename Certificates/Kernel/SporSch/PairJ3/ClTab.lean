module

public import Certificates.Kernel.SporSch.PairJ3.ClFns
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.SporSch.PairClTSound
public import CFSG.Certificates.Kernel.SporSch.PairKSound

public section

set_option maxRecDepth 400000

#kss_each CertificateChecks.KernelSporSch.PJ3Cl.TS CertificateChecks.KernelSporSch.PJ3Cl.tsB 4
#kss_each CertificateChecks.KernelSporSch.PJ3Cl.LTc CertificateChecks.KernelSporSch.PJ3Cl.ltB 61
#kss_b2 CertificateChecks.KernelSporSch.PJ3Cl CertificateChecks.KernelSporSch.PJ3Cl.ptB 0 4 7
#kss_b2all CertificateChecks.KernelSporSch.PJ3Cl CertificateChecks.KernelSporSch.PJ3Cl.ptB 4 7
#kss_b2 CertificateChecks.KernelSporSch.PJ3Cl CertificateChecks.KernelSporSch.PJ3Cl.qtB 0 4 7
#kss_b2all CertificateChecks.KernelSporSch.PJ3Cl CertificateChecks.KernelSporSch.PJ3Cl.qtB 4 7

end
