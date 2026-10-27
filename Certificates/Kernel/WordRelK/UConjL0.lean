module

public import Certificates.Kernel.WordRelK.Tab
public import Certificates.Data.Kernel.WordRelK
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 400000

public section

open CFSG.KC.WordRelK CertificateChecks.KernelWordRelK.Tab in
#kc_each CertificateChecks.KernelWordRelK.UConjL ucl (uConjLRowT TAB) 0 5

end
