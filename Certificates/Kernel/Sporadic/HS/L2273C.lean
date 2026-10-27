module

public import Certificates.Kernel.Sporadic.HS.L2273D
public import Certificates.Kernel.LocalQT.HSAut.D4146
public import Certificates.Data.Kernel.Spor.HSL2273
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HSL

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.HSL

theorem c1_comm : Nat.beq (cntK (fun i => commK Q.G (CFSG.KD.LQT.HN.A.T i)) 120) 4 = true := by
  quickRfl

end CFSG.KD.HSL

end
