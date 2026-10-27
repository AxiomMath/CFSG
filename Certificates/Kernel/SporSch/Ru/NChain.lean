module

public import Certificates.Kernel.SporSch.Ru.CPLvN
public import Certificates.Kernel.SporSch.Ru.NUSch0
public import Certificates.Kernel.SporSch.Ru.NUSch1
public import Certificates.Kernel.SporSch.Ru.NUSch2
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_joing CertificateChecks.KernelSporSch.RuNS CertificateChecks.KernelSporSch.RuNW.W

end
