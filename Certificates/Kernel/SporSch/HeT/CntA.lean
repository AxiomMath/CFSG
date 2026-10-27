module

public import Certificates.Kernel.SporSch.HeT.CntAH
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.SporSch.HeSrchSplit

public section

set_option maxRecDepth 400000

set_option maxHeartbeats 0 in
#kss_each CertificateChecks.KernelSporSch.HeCn.OA CertificateChecks.KernelSporSch.HeCn.orA 49

end
