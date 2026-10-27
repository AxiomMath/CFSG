module

public import Certificates.Kernel.SporSch.Ru.EndChecks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_each CertificateChecks.KernelSporSch.RuEndEl CertificateChecks.KernelSporSch.RuEnd.elemOK 256

end
