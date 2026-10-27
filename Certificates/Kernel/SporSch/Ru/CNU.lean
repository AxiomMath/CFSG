module

public import Certificates.Kernel.SporSch.Ru.CData
public import Certificates.Kernel.Sporadic.RawGenSchPU
meta import Certificates.Kernel.SporSch.Ru.CData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_utab CertificateChecks.KernelSporSch.RuCS
  CertificateChecks.KernelSporSch.RuCN.strongC CertificateChecks.KernelSporSch.RuCN.baseC

#ks_rawchain_sl2_utab CertificateChecks.KernelSporSch.RuNS
  CertificateChecks.KernelSporSch.RuCN.strongN CertificateChecks.KernelSporSch.RuCN.baseN

end
