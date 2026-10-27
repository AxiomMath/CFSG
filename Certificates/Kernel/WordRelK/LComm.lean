module

public import Certificates.Kernel.WordRelK.Tab
public import Certificates.Data.Kernel.WordRelK
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 400000

public section

open CFSG.KC.WordRelK CertificateChecks.KernelWordRelK.Tab in
#kc_each CertificateChecks.KernelWordRelK.LComm lc (lCommRowT TAB) 0 16

open CFSG.KC.WordRelK CertificateChecks.KernelWordRelK.Tab in
#kc_each CertificateChecks.KernelWordRelK.LComm lsq (lSqT TAB) 0 16

end
