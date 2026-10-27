module

public import Certificates.Kernel.SporSch.HeT.CntData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_each CertificateChecks.KernelSporSch.HeCn.CT CertificateChecks.KernelSporSch.HeCn.cjT 49
set_option maxHeartbeats 0 in
#kss_each CertificateChecks.KernelSporSch.HeCn.OT CertificateChecks.KernelSporSch.HeCn.orT 49

end
