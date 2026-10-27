module

public import Certificates.Kernel.LyGlue.Prog2
public import CFSG.Certificates.Kernel.Common.SliceRange

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

#kc_slice_range CertificateChecks.KernelLy.stepK CertificateChecks.KernelLy.st 0 5

end
