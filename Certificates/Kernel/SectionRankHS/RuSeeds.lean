module

public import Certificates.Kernel.LocalComp.M1Gen
import all CFSG.Blueprint.NativeSporadic
meta import CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

public section

#ks_chars CertificateChecks.KernelSRHS.RA CFSG.Blueprint.NativeSporadic.RuSeed1
#lc_m1 CertificateChecks.KernelSRHS.RA CFSG.Blueprint.NativeSporadic.RuSeed1 28
#ks_chars CertificateChecks.KernelSRHS.RB CFSG.Blueprint.NativeSporadic.RuSeed2
#lc_m1 CertificateChecks.KernelSRHS.RB CFSG.Blueprint.NativeSporadic.RuSeed2 28

end
