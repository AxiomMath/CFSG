module

public import Certificates.Kernel.U43Triple.Data
public import CFSG.LieType.Multipliers.U43Data
public import Certificates.Data.Kernel.Multipliers.BindList
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.Open.Defs

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelU43T

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.BindList CFSG.LieType.Multipliers.U43

theorem canonX : CFSG.KC.LQT.P.allN 2 (fun i => canonK 820 10 (mask 10) 8200 (X i)) = true := by
  decide +kernel

theorem bindTA : bindListK 10 (mask 10) (X 0) tabA.toList 0 = true := by quickRfl

theorem bindTB : bindListK 10 (mask 10) (X 1) tabB.toList 0 = true := by quickRfl

end CertificateChecks.KernelU43T

end
