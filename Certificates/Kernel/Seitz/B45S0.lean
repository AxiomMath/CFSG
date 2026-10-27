module

public import Certificates.Kernel.Seitz.B45
public import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

#kc_each CertificateChecks.KernelSeitz.sliceK 0 4

end
