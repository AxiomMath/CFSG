module

public import Certificates.Kernel.KGC31HS.Defs
public import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

#kc_each CertificateChecks.KernelKGC31HS.invBlk 6 12

end
