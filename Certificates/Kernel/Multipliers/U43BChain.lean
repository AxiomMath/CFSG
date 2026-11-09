module

public import Certificates.Kernel.Sporadic.RawGenSchOJ
public import Certificates.Kernel.Multipliers.U43BData
meta import Certificates.Kernel.Multipliers.U43BData
public meta import Certificates.Kernel.Sporadic.RawGenSchOJ
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43Data
public import CFSG.Open.Defs
meta import CFSG.Certificates.CosetTableShort
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.LieType.Multipliers.ProductKernel
meta import CFSG.LieType.Multipliers.U43Action
meta import CFSG.LieType.Multipliers.U43Data
meta import CFSG.Open.Defs

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_data CertificateChecks.KernelU43B.C 820 10 64 64 CFSG.LieType.Multipliers.U43.chainS
  CertificateChecks.KernelU43B.base 2 CertificateChecks.KernelU43B.der

#ks_rawchain_sl2_lv CertificateChecks.KernelU43B.C 0 0 13
#ks_rawchain_sl2_lv CertificateChecks.KernelU43B.C 1 0 13
#ks_rawchain_sl2_lv CertificateChecks.KernelU43B.C 2 0 13

#ks_rawchain_sl2_sch CertificateChecks.KernelU43B.C 1 0 4
#ks_rawchain_sl2_sch CertificateChecks.KernelU43B.C 2 0 1

#ks_rawchain_sl2_osub CertificateChecks.KernelU43B.C
#ks_rawchain_sl2_scho CertificateChecks.KernelU43B.C 0 9

#ks_rawchain_sl2_joino CertificateChecks.KernelU43B.C

end
