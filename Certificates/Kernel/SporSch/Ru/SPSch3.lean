module

public import Certificates.Kernel.SporSch.Ru.SData
public import Certificates.Kernel.Sporadic.RawGenSchP
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_schp CertificateChecks.KernelSporSch.RuSS 0 768 1024
#ks_rawchain_sl2_schp CertificateChecks.KernelSporSch.RuSS 1 0 4

end
