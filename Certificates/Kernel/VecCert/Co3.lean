module

public import Certificates.Kernel.VecCert.Gen
public import Certificates.Data.CFSGNative.Co3.Data
public meta import Certificates.Data.CFSGNative.Co3.Data

public section

set_option maxRecDepth 200000

#kvec CertificateChecks.KernelVec.Co3 CFSG.Sporadic.Co3.Native.co3Data 256

end
