module

public import Certificates.Kernel.LocalComp.U43Arrs
public import Certificates.Kernel.Sporadic.RawGenSplit
meta import Certificates.Kernel.LocalComp.U43Arrs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.Open.Defs
meta import CFSG.Certificates.CosetTableShort
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.LieType.Multipliers.ProductKernel
meta import CFSG.Open.Defs

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_data CertificateChecks.KernelLC.U43.UA 820 10 64 64
  CFSG.EvenSmallLie.Child3.SelU43.autS CertificateChecks.KernelLC.U43.autBaseArr 4
  CFSG.EvenSmallLie.Child3.SelU43.autWords

#ks_rawchain_sl2_data CertificateChecks.KernelLC.U43.US 820 10 64 64
  CFSG.EvenSmallLie.Child3.SelU43.sylowS CertificateChecks.KernelLC.U43.sylowBaseArr 4
  CFSG.EvenSmallLie.Child3.SelU43.sylowWords

end
