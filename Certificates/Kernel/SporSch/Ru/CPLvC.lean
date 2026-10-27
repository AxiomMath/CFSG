module

public import Certificates.Kernel.SporSch.Ru.CData
public import Certificates.Kernel.Sporadic.RawGenSplitP
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_lvp CertificateChecks.KernelSporSch.RuCS 0 0 64
#ks_rawchain_sl2_lvp CertificateChecks.KernelSporSch.RuCS 1 0 64
#ks_rawchain_sl2_lvp CertificateChecks.KernelSporSch.RuCS 2 0 64

end
