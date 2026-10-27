module

public import Certificates.Kernel.HS589207.M
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.BfsRecK

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HS589207.E0

open CFSG.KC.DcHSOutK CFSG.KC.Enum

theorem fix : allN 11520 (fun k => fixF0 (mF k) == I0.contains k) = true := by quickRfl

theorem idx : (decide I0.Nodup && I0.all (fun k => Nat.blt k 11520) && decide IO.Nodup &&
    IO.all (fun k => Nat.blt k 11520)) = true := by
  quickRfl

end CFSG.KD.HS589207.E0

end
