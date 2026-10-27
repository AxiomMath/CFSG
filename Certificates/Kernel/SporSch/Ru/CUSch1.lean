module

public import Certificates.Kernel.SporSch.Ru.CNG
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_schg CertificateChecks.KernelSporSch.RuCS 480 960
#ks_rawchain_sl2_sch CertificateChecks.KernelSporSch.RuCS 1 0 32
#ks_rawchain_sl2_sch CertificateChecks.KernelSporSch.RuCS 2 0 1

end
