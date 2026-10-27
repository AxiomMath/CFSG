module

public import Certificates.Kernel.VecCert.Gen
public import Certificates.Data.CFSGNative.HS.Data
public meta import Certificates.Data.CFSGNative.HS.Data

public section

set_option maxRecDepth 200000

#kvec CertificateChecks.KernelVec.HS CFSG.Sporadic.HS.Native.hsData 256

end
