module

public import Certificates.Kernel.VecCert.Gen
public import Certificates.Data.CFSGNative.Ru.Data
public meta import Certificates.Data.CFSGNative.Ru.Data

public section

set_option maxRecDepth 200000

#kvec CertificateChecks.KernelVec.Ru CFSG.Sporadic.Ru.Native.ruData 256

end
