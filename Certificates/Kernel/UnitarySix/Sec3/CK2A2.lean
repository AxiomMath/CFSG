module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.UnitarySix.Sec3.Arrs
public import Certificates.Kernel.Sporadic.RawGenSchPFJ
public import Certificates.Kernel.UnitarySix.Sec3.CK2A2D
public import Certificates.Kernel.UnitarySix.Sec3.CK2A2Lv
public import Certificates.Kernel.UnitarySix.Sec3.CK2A2F0
public import Certificates.Kernel.UnitarySix.Sec3.CK2A2F1
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_joinpf CertificateChecks.KernelU6.Sec3.CK2A2 7

end
