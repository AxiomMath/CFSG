module

public import Certificates.Kernel.SporSch.Ru.JCData
public import Certificates.Kernel.Sporadic.RawGenSplitP
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_lvp CertificateChecks.KernelSporSch.RuJS 2 0 254
#ks_rawchain_sl2_lvp CertificateChecks.KernelSporSch.RuJS 3 0 254

end
