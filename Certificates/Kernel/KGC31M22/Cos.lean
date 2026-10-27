module

public import Certificates.Kernel.KGC31M22.Defs
public import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000
#kc_each CertificateChecks.KernelKGC31M22.cosBlk 0 3

end
