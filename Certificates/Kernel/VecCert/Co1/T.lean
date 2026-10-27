module

public import Certificates.Kernel.VecCert.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Data

public section

set_option maxRecDepth 200000

#kvec CertificateChecks.KernelVec.Co1 CFSG.Sporadic.Co1.Native.co1Data 256 "tree*,sub*"

end
