module

public import Certificates.Kernel.LocalQT.M11.Data
public import CFSG.Certificates.Kernel.LocalQTM11Base
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8M11DataInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M11CheckInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadM11Inputs

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4154

open CFSG.KC.LQT.M CFSG.KC.LQT.S CFSG.KD.LQT.M11 CFSG.QuasithinUnique.Unc25M11
  CFSG.Sporadic.Mathieu

@[expose] def LP : List Nat := [11584701642934304, 3420860021279008, 148718781238598, 1486782563617926, 6834809262638089, 11266973921117257, 10246626053466308, 220144087640164, 4547824010330402, 7080041157623842, 2611616235690115, 10282873430022467, 3386747243340865, 4581946451665921, 1344977775956074, 2366399372628170]

theorem hsa : code sa = 148718781238598 := by decide +kernel
theorem hsb : code sb = 3420860021279008 := by decide +kernel
theorem hp : P0L.map code = LP := by decide +kernel
theorem hk : c4154 R1 R2 R3 R4 LP 148718781238598 3420860021279008 = true := by quickRfl

end CFSG.KD.LQT.C4154

end
