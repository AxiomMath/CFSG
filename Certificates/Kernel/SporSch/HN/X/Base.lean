module

public import CFSG.Certificates.Kernel.Local.HN.X.Lib
public import CFSG.Certificates.Kernel.Local.HN.X.Data
public import CFSG.Certificates.Kernel.Orders.HN.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Local.HN.Lib
public import CFSG.Certificates.Kernel.Local.LargeCore.Grp2

public section

namespace CFSG.KD.LgHNX

open CFSG.KC.LL CFSG.KC.LL.HNX

theorem consts : CFSG.KC.Ord.andB (constsOK CM3 M) (masksOK MS) = true := by quickRfl

theorem bindA : Nat.beq (trM (CFSG.KD.OrdHN.RW 1)) GA = true := by quickRfl

theorem bindB : Nat.beq (trM (CFSG.KD.OrdHN.RW 2)) GB = true := by quickRfl

theorem rec0 : CFSG.KC.Ord.andB (Nat.beq (Nat.land (getRec TX 464 0) M) V0C)
    (Nat.beq (spread MS V0C) V0) = true := by quickRfl

end CFSG.KD.LgHNX

end
