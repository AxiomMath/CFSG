module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.UnitarySix.Sec3.Arrs
public import Certificates.Kernel.Sporadic.RawGenSchPU
public import Certificates.Kernel.UnitarySix.Sec3.CLU
public import Certificates.Kernel.UnitarySix.Sec3.CLLv
public import Certificates.Kernel.UnitarySix.Sec3.CLF0
public import Certificates.Kernel.UnitarySix.Sec3.CLF1
public import Certificates.Kernel.UnitarySix.Sec3.CLF2
public import Certificates.Kernel.UnitarySix.Sec3.CLF3
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_joinpfu CertificateChecks.KernelU6.Sec3.CL 31 7

end
