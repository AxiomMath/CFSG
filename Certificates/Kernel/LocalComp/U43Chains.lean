module

public import Certificates.Kernel.LocalComp.U43CA0
public import Certificates.Kernel.LocalComp.U43CA1
public import Certificates.Kernel.LocalComp.U43CA2
public import Certificates.Kernel.LocalComp.U43CS
public import Certificates.Kernel.Sporadic.RawGenSchPFJ
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_joinpf CertificateChecks.KernelLC.U43.UA 31

#ks_rawchain_sl2_joinpf CertificateChecks.KernelLC.U43.US 3

end
