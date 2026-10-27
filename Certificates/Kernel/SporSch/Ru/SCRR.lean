module

public import Certificates.Kernel.SporSch.Ru.SCRData
public import Certificates.Kernel.Sporadic.RawGenSplitP
public import Certificates.Kernel.Sporadic.RawGenSchPFJ
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_lvp CertificateChecks.KernelSporSch.RuRS2 0 0 120
#ks_rawchain_sl2_lvp CertificateChecks.KernelSporSch.RuRS2 1 0 120
#ks_rawchain_sl2_schpf CertificateChecks.KernelSporSch.RuRS2 0 0 128
#ks_rawchain_sl2_schp CertificateChecks.KernelSporSch.RuRS2 1 0 4

#ks_rawchain_sl2_joinpf CertificateChecks.KernelSporSch.RuRS2 1

end
