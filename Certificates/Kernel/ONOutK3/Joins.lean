module

public import Certificates.Kernel.ONOutK3.N0
public import Certificates.Kernel.ONOutK3.N1
public import Certificates.Kernel.ONOutK3.N2
public import Certificates.Kernel.ONOutK3.N3
public import Certificates.Kernel.ONOutK3.N4
public import Certificates.Kernel.ONOutK3.N5
public import Certificates.Kernel.ONOutK3.N6
public import Certificates.Kernel.ONOutK3.N7
public import Certificates.Kernel.ONOutK3.N8
public import Certificates.Kernel.ONOutK3.Sorted
public import Certificates.Kernel.ONOutK3.MatChk
public import Certificates.Kernel.ONOutK3.FChk

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.ONK3.nAll CertificateChecks.KernelSpor.ONK3.nsl 315
#kon_join CertificateChecks.KernelSpor.ONK3.sAll CertificateChecks.KernelSpor.ONK3.ssl 64
#kon_join CertificateChecks.KernelSpor.ONK3.mAll CertificateChecks.KernelSpor.ONK3.mchk 37
#kon_join CertificateChecks.KernelSpor.ONK3.fAll4 CertificateChecks.KernelSpor.ONK3.fchk 4

end
