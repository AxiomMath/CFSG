module

public import Certificates.Kernel.UnitarySix.Sec3.CLU
public import Certificates.Kernel.Sporadic.RawGenSplitP
public import Certificates.Kernel.Sporadic.RawGenSchPUS
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_lvp CertificateChecks.KernelU6.Sec3.CL 0 0 11
#ks_rawchain_sl2_lvp CertificateChecks.KernelU6.Sec3.CL 1 0 11
#ks_rawchain_sl2_lvp CertificateChecks.KernelU6.Sec3.CL 2 0 11
#ks_rawchain_sl2_lvp CertificateChecks.KernelU6.Sec3.CL 3 0 11
#ks_rawchain_sl2_lvp CertificateChecks.KernelU6.Sec3.CL 4 0 11
#ks_rawchain_sl2_schpus CertificateChecks.KernelU6.Sec3.CL 2 0 3 1
#ks_rawchain_sl2_schpf CertificateChecks.KernelU6.Sec3.CL 3 0 1
#ks_rawchain_sl2_schpf CertificateChecks.KernelU6.Sec3.CL 4 0 1

end
