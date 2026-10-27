module

public import Certificates.Kernel.HS589206.E16M
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.BfsRecK
public import Certificates.Data.Kernel.HS589206E16
public import Certificates.Kernel.HS589207.M

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HS589206.E16RecA

open CFSG.KC.DcK CFSG.KD.HS589206.E16 CFSG.Quasithin.H13.LocDbl.HSLoc

theorem hd : enumHd 100 B100 600 ES = true := by quickRfl

theorem s0 : elemsK 100 B100 GS 3 ES 0 256 = true := by quickRfl

end CFSG.KD.HS589206.E16RecA

end
