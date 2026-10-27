module

public import Certificates.Kernel.HNChain.Data
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.HNChain

open CFSG.KC.HNLocal

theorem tr1 : Nat.beq (treeSum XC1 TD1 CFSG.KD.HNLocal.MSF 10395 CFSG.KD.HNLocal.M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CFSG.KD.HNLocal.CM3 CFSG.KD.OrdHN.RM G10 G11 CFSG.KD.OrdHN.ONE 0 79) 0 = true := by
  quickRfl

theorem so1 : sortRange XC1 SD1 10395 CFSG.KD.HNLocal.M 0 79 = true := by quickRfl

end CFSG.KD.HNChain

end
