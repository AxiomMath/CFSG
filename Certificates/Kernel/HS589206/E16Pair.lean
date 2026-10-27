module

public import Certificates.Kernel.HS589206.E16M
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.BfsRecK
public import Certificates.Data.Kernel.HS589206E16
public import Certificates.Kernel.HS589207.M

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HS589206.E16Pair

open CFSG.KC.HS589206E16 CFSG.KD.HS589206.E16

theorem invs : invsK sF 512 ix 87 = true := by quickRfl

theorem p0 : pairsK IF PT 87 0 44 = true := by quickRfl

theorem p1 : pairsK IF PT 87 44 43 = true := by quickRfl

end CFSG.KD.HS589206.E16Pair

end
