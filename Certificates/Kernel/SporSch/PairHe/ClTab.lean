module

public import Certificates.Kernel.SporSch.PairHe.ClFns
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_each CertificateChecks.KernelSporSch.PHeCl.TS CertificateChecks.KernelSporSch.PHeCl.tsB 5
#kss_each CertificateChecks.KernelSporSch.PHeCl.LTc CertificateChecks.KernelSporSch.PHeCl.ltB 147
#kss_b2 CertificateChecks.KernelSporSch.PHeCl CertificateChecks.KernelSporSch.PHeCl.ptB 0 5 9
#kss_b2all CertificateChecks.KernelSporSch.PHeCl CertificateChecks.KernelSporSch.PHeCl.ptB 5 9
#kss_b2 CertificateChecks.KernelSporSch.PHeCl CertificateChecks.KernelSporSch.PHeCl.qtB 0 5 9
#kss_b2all CertificateChecks.KernelSporSch.PHeCl CertificateChecks.KernelSporSch.PHeCl.qtB 5 9

end
