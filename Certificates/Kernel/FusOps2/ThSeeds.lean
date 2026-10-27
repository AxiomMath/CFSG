module

public import Certificates.Kernel.LocalComp.M1Gen
import all CFSG.Blueprint.NativeSporadic
meta import CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

public section

#ks_chars CertificateChecks.KernelFusOps2.TA CFSG.Blueprint.NativeSporadic.ThSeed1
#lc_m1 CertificateChecks.KernelFusOps2.TA CFSG.Blueprint.NativeSporadic.ThSeed1 248
#ks_chars CertificateChecks.KernelFusOps2.TB CFSG.Blueprint.NativeSporadic.ThSeed2
#lc_m1 CertificateChecks.KernelFusOps2.TB CFSG.Blueprint.NativeSporadic.ThSeed2 248

end
