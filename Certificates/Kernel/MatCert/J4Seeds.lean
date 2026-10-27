module

public import Certificates.Kernel.LocalComp.M1Gen
import all CFSG.Blueprint.NativeSporadic
meta import CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

public section

#ks_chars CertificateChecks.KernelMC.JA CFSG.Blueprint.NativeSporadic.J4Seed1
#lc_m1 CertificateChecks.KernelMC.JA CFSG.Blueprint.NativeSporadic.J4Seed1 112
#ks_chars CertificateChecks.KernelMC.JB CFSG.Blueprint.NativeSporadic.J4Seed2
#lc_m1 CertificateChecks.KernelMC.JB CFSG.Blueprint.NativeSporadic.J4Seed2 112

end
