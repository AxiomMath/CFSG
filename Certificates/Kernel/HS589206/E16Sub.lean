module

public import Certificates.Kernel.HS589206.E16M2
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.BfsRecK
public import Certificates.Data.Kernel.HS589206E16B
public import Certificates.Kernel.HS589206.E16M
public import Certificates.Kernel.HS589207.M

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HS589206.E16Sub

open CFSG.KC.HS589206E16 CFSG.KD.HS589206.E16 CFSG.KD.HS589207 CFSG.Quasithin.H13.LocDbl.HSLoc

theorem subs : CFSG.KC.Enum.allN 8 (fun t => eT IF A F0 87 (MK t) (eR t)) = true := by quickRfl

theorem fix5 : fix5K s5F 125 5 = true := by quickRfl

end CFSG.KD.HS589206.E16Sub

end
