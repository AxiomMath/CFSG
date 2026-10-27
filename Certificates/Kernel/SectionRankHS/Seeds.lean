module

public import Certificates.Kernel.LocalComp.M1Gen
import all CFSG.Blueprint.NativeSporadic
meta import CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

public section

#ks_chars CertificateChecks.KernelSRHS.SA CFSG.Blueprint.NativeSporadic.HSSeed1
#lc_m1 CertificateChecks.KernelSRHS.SA CFSG.Blueprint.NativeSporadic.HSSeed1 20
#ks_chars CertificateChecks.KernelSRHS.SB CFSG.Blueprint.NativeSporadic.HSSeed2
#lc_m1 CertificateChecks.KernelSRHS.SB CFSG.Blueprint.NativeSporadic.HSSeed2 20

end
