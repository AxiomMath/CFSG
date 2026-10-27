module

public import Certificates.Kernel.LocalComp.M1Gen
public import Certificates.Data.CFSGNative.J3.Data
meta import Certificates.Data.CFSGNative.J3.Data

set_option maxRecDepth 400000

public section

#ks_chars CertificateChecks.KernelLC.J3Ops.SA CFSG.Sporadic.J3.Native.seedA
#lc_m1 CertificateChecks.KernelLC.J3Ops.SA CFSG.Sporadic.J3.Native.seedA 80
#ks_chars CertificateChecks.KernelLC.J3Ops.SB CFSG.Sporadic.J3.Native.seedB
#lc_m1 CertificateChecks.KernelLC.J3Ops.SB CFSG.Sporadic.J3.Native.seedB 80

end
