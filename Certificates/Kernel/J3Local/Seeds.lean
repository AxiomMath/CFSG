module

public import Certificates.Kernel.LocalComp.M1Gen
import all CFSG.Blueprint.NativeSporadic
meta import CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

public section

#ks_chars CertificateChecks.KernelJ3L.JA CFSG.Blueprint.NativeSporadic.J3Seed1
#lc_m1 CertificateChecks.KernelJ3L.JA CFSG.Blueprint.NativeSporadic.J3Seed1 80
#ks_chars CertificateChecks.KernelJ3L.JB CFSG.Blueprint.NativeSporadic.J3Seed2
#lc_m1 CertificateChecks.KernelJ3L.JB CFSG.Blueprint.NativeSporadic.J3Seed2 80

end
