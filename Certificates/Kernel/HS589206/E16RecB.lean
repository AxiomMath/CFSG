module

public import Certificates.Kernel.HS589206.E16M
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.BfsRecK
public import Certificates.Data.Kernel.HS589206E16
public import Certificates.Kernel.HS589207.M

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HS589206.E16RecB

open CFSG.KC.DcK CFSG.KD.HS589206.E16 CFSG.Quasithin.H13.LocDbl.HSLoc

theorem s1 : elemsK 100 B100 GS 3 ES 256 256 = true := by quickRfl

end CFSG.KD.HS589206.E16RecB

end
