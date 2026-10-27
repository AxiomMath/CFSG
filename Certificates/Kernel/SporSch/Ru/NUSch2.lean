module

public import Certificates.Kernel.SporSch.Ru.CNG
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_schg CertificateChecks.KernelSporSch.RuNS 1200 1792
#ks_rawchain_sl2_sch CertificateChecks.KernelSporSch.RuNS 1 0 24
#ks_rawchain_sl2_sch CertificateChecks.KernelSporSch.RuNS 2 0 1

end
