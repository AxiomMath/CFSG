module

public import Certificates.Kernel.VecCert.Gen
public import Certificates.Data.CFSGNative.Co2.Data
public meta import Certificates.Data.CFSGNative.Co2.Data

public section

set_option maxRecDepth 200000

#kvec CertificateChecks.KernelVec.Co2 CFSG.Sporadic.Co2.Native.co2Data 256

end
