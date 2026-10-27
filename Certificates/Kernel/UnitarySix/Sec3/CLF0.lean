module

public import Certificates.Kernel.UnitarySix.Sec3.CLU
public import Certificates.Kernel.Sporadic.RawGenSchPUS
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_schpus CertificateChecks.KernelU6.Sec3.CL 0 0 4 1

end
