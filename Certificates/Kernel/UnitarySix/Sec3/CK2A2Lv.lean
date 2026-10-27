module

public import Certificates.Kernel.UnitarySix.Sec3.CK2A2D
public import Certificates.Kernel.Sporadic.RawGenSplitP
public import Certificates.Kernel.Sporadic.RawGenSchPF
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_lvp CertificateChecks.KernelU6.Sec3.CK2A2 0 0 11
#ks_rawchain_sl2_lvp CertificateChecks.KernelU6.Sec3.CK2A2 1 0 11
#ks_rawchain_sl2_lvp CertificateChecks.KernelU6.Sec3.CK2A2 2 0 11
#ks_rawchain_sl2_schpf CertificateChecks.KernelU6.Sec3.CK2A2 1 0 8
#ks_rawchain_sl2_schpf CertificateChecks.KernelU6.Sec3.CK2A2 2 0 1

end
