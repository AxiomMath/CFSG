module

public import Certificates.Kernel.SporSch.Ru.SCRData
public import Certificates.Kernel.Sporadic.RawGenSplitP
public import Certificates.Kernel.Sporadic.RawGenSchPJ
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_lvp CertificateChecks.KernelSporSch.RuJS2 0 0 120
#ks_rawchain_sl2_lvp CertificateChecks.KernelSporSch.RuJS2 1 0 120
#ks_rawchain_sl2_schp CertificateChecks.KernelSporSch.RuJS2 0 0 64
#ks_rawchain_sl2_schp CertificateChecks.KernelSporSch.RuJS2 1 0 8

#ks_rawchain_sl2_joinp CertificateChecks.KernelSporSch.RuJS2

end
