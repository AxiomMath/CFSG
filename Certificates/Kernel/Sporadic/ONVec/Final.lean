module

public import Certificates.Kernel.Sporadic.ONVec.Sig0
public import Certificates.Kernel.Sporadic.ONVec.Sig1
public import Certificates.Kernel.Sporadic.ONVec.Sig2
public import Certificates.Kernel.Sporadic.ONVec.Sig3
public import Certificates.Kernel.Sporadic.ONVec.Sig4
public import Certificates.Kernel.Sporadic.ONVec.Sig5
public import Certificates.Kernel.Sporadic.ONVec.Sig6
public import Certificates.Kernel.Sporadic.ONVec.Sig7
public import Certificates.Kernel.Sporadic.ONVec.Sort0
public import Certificates.Kernel.Sporadic.ONVec.Sort1
public import Certificates.Kernel.Sporadic.ONVec.Sort2
public import Certificates.Kernel.Sporadic.ONVec.Sort3
public import Certificates.Kernel.Sporadic.ONVec.Sort4
public import Certificates.Kernel.Sporadic.ONVec.Sort5
public import Certificates.Kernel.Sporadic.ONVec.Sort6
public import Certificates.Kernel.Sporadic.ONVec.Sort7

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.ONVec.sigAll CertificateChecks.KernelSpor.ONVec.sigS 1023

#kon_join CertificateChecks.KernelSpor.ONVec.ssortAll CertificateChecks.KernelSpor.ONVec.ssortS 1023

end
