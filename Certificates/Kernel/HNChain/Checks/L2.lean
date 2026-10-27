module

public import Certificates.Kernel.HNChain.Data
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.HNChain

open CFSG.KC.HNLocal

theorem tr2 : Nat.beq (treeSum XC2 TD2 CFSG.KD.HNLocal.MSF 720 CFSG.KD.HNLocal.M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CFSG.KD.HNLocal.CM3 CFSG.KD.OrdHN.RM G20 G21 CFSG.KD.OrdHN.ONE 0 6) 0 = true := by
  quickRfl

theorem so2 : sortRange XC2 SD2 720 CFSG.KD.HNLocal.M 0 6 = true := by quickRfl

end CFSG.KD.HNChain

end
