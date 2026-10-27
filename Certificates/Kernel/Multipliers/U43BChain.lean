module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Multipliers.U43BData
meta import Certificates.Kernel.Multipliers.U43BData
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

#ks_rawchain CertificateChecks.KernelU43B.C 820 10 64 CFSG.LieType.Multipliers.U43.chainS
  CertificateChecks.KernelU43B.base 2 CertificateChecks.KernelU43B.der

end
