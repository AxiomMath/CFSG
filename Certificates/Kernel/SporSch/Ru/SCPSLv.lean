module

public import Certificates.Kernel.SporSch.Ru.SCData
public import Certificates.Kernel.Sporadic.RawGenSplitP
public import Certificates.Kernel.Sporadic.RawGenSchP
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_lvp CertificateChecks.KernelSporSch.RuSS2 0 0 120
#ks_rawchain_sl2_lvp CertificateChecks.KernelSporSch.RuSS2 1 0 120
#ks_rawchain_sl2_schp CertificateChecks.KernelSporSch.RuSS2 1 0 8

end
