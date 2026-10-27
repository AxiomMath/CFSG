module

public import Certificates.Kernel.SporSch.Ru.SCData
public import Certificates.Kernel.Sporadic.RawGenSchPF
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_schpf CertificateChecks.KernelSporSch.RuFS 0 0 480

end
