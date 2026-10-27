module

public import Certificates.Kernel.HS589206.E16M
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.BfsRecK
public import Certificates.Data.Kernel.HS589206E16
public import Certificates.Kernel.HS589207.M

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HS589206.E16QuadB

open CFSG.KC.HS589206E16 CFSG.KD.HS589206.E16

theorem q1 : quadBlk PT MK 8 87 15 15 = true := by quickRfl

end CFSG.KD.HS589206.E16QuadB

end
