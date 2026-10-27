module

public import Certificates.Kernel.SporSch.Ru.LCData
public import Certificates.Kernel.Sporadic.RawGenSplitP
public import Certificates.Kernel.Sporadic.RawGenSchP
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_lvp CertificateChecks.KernelSporSch.RuLS 0 0 508
#ks_rawchain_sl2_lvp CertificateChecks.KernelSporSch.RuLS 1 0 508
#ks_rawchain_sl2_schp CertificateChecks.KernelSporSch.RuLS 1 0 32

end
