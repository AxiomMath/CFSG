module

public import Certificates.Kernel.SporSch.Ru.CPLvC
public import Certificates.Kernel.SporSch.Ru.CUSch0
public import Certificates.Kernel.SporSch.Ru.CUSch1
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_joing CertificateChecks.KernelSporSch.RuCS CertificateChecks.KernelSporSch.RuCW.W

end
