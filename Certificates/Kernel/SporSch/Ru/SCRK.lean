module

public import Certificates.Kernel.SporSch.Ru.SCRData
public import Certificates.Kernel.Sporadic.RawGenSplitP
public import Certificates.Kernel.Sporadic.RawGenSchPJ
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_lvp CertificateChecks.KernelSporSch.RuKS 0 0 120
#ks_rawchain_sl2_lvp CertificateChecks.KernelSporSch.RuKS 1 0 120
#ks_rawchain_sl2_schp CertificateChecks.KernelSporSch.RuKS 0 0 256
#ks_rawchain_sl2_schp CertificateChecks.KernelSporSch.RuKS 1 0 2

#ks_rawchain_sl2_joinp CertificateChecks.KernelSporSch.RuKS

end
