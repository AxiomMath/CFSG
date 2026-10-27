module

public import Certificates.Kernel.HNLocal.XData
public import Certificates.Kernel.HNLocal.TreeData
public import Certificates.Kernel.HNLocal.Data
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNLocal

theorem tr4 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x860) (nat_lit 0x218))
    (nat_lit 0x5800023d) = true := by
  quickRfl

end CFSG.KD.HNLocal

end
