module

public import Certificates.Kernel.SporSch.HeThree.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

set_option maxHeartbeats 0 in
#kss_each CertificateChecks.KernelSporSch.HeThree.OR0c CertificateChecks.KernelSporSch.HeThree.or0 49
set_option maxHeartbeats 0 in
#kss_each CertificateChecks.KernelSporSch.HeThree.OR1c CertificateChecks.KernelSporSch.HeThree.or1 49

end
