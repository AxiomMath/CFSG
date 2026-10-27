module

public import Certificates.Kernel.SporSch.PairHS.ClFns
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_each CertificateChecks.KernelSporSch.PHSCl.TS CertificateChecks.KernelSporSch.PHSCl.tsB 4
#kss_each CertificateChecks.KernelSporSch.PHSCl.LTc CertificateChecks.KernelSporSch.PHSCl.ltB 61
#kss_b2 CertificateChecks.KernelSporSch.PHSCl CertificateChecks.KernelSporSch.PHSCl.ptB 0 4 4
#kss_b2all CertificateChecks.KernelSporSch.PHSCl CertificateChecks.KernelSporSch.PHSCl.ptB 4 4
#kss_b2 CertificateChecks.KernelSporSch.PHSCl CertificateChecks.KernelSporSch.PHSCl.qtB 0 4 4
#kss_b2all CertificateChecks.KernelSporSch.PHSCl CertificateChecks.KernelSporSch.PHSCl.qtB 4 4

end
