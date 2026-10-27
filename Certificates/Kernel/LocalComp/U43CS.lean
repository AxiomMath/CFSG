module

public import Certificates.Kernel.LocalComp.U43CData
public import Certificates.Kernel.Sporadic.RawGenSplitP
public import Certificates.Kernel.Sporadic.RawGenSchPF
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_lvp CertificateChecks.KernelLC.U43.US 0 0 13
#ks_rawchain_sl2_lvp CertificateChecks.KernelLC.U43.US 1 0 13

#ks_rawchain_sl2_schpf CertificateChecks.KernelLC.U43.US 0 0 4
#ks_rawchain_sl2_schpf CertificateChecks.KernelLC.U43.US 1 0 1

end
