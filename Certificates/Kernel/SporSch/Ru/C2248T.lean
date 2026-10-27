module

public import Certificates.Kernel.SporSch.Ru.C2248
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_each CertificateChecks.KernelSporSch.RuCt.TS CertificateChecks.KernelSporSch.RuCt.tstep 120
#kss_each CertificateChecks.KernelSporSch.RuCt.TD CertificateChecks.KernelSporSch.RuCt.tdist 120
#kss_each CertificateChecks.KernelSporSch.RuCt.TC CertificateChecks.KernelSporSch.RuCt.tcan 120

end
