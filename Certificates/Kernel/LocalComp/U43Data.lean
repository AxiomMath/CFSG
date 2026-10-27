module

public import Certificates.Kernel.LocalComp.U43Binds
public import Certificates.Kernel.LocalComp.Child3Gen
meta import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelU43Data
import CFSG.Certificates.Kernel.Common.Harness
meta import CFSG.Certificates.CosetTableShort
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.LieType.Multipliers.ProductKernel
meta import CFSG.Open.Defs

public section

set_option maxRecDepth 400000

#lc_forest CertificateChecks.KernelLC.U43.UF 820 CFSG.LieType.Multipliers.U43.chainS [0, 4]

#lc_reps CertificateChecks.KernelLC.U43.UR 10 CFSG.EvenSmallLie.Child3.SelU43.sylowGens
  CFSG.EvenSmallLie.Child3.SelU43.repArrs

end
