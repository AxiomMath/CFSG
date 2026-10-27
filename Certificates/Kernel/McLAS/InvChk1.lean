module

public import Certificates.Kernel.McLAS.InvRec
public import CFSG.Certificates.Kernel.Common.SliceRange

public section

set_option maxRecDepth 400000

#kc_slice_range CertificateChecks.KernelMcLAS.ipSl CertificateChecks.KernelMcLAS.InvChk.ci 56 112

end
