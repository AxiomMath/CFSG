module

public import Certificates.Kernel.HS589207.M
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.BfsRecK

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HS589207.MRecB

open CFSG.KC.DcK CFSG.KC.DcHSOutK CFSG.KC.Enum CFSG.Quasithin.H13.LocDbl.HSLoc

theorem s4 : elemsK 100 B100 GM 2 EM 5760 1440 = true := by quickRfl

theorem s5 : elemsK 100 B100 GM 2 EM 7200 1440 = true := by quickRfl

theorem s6 : elemsK 100 B100 GM 2 EM 8640 1440 = true := by quickRfl

theorem s7 : elemsK 100 B100 GM 2 EM 10080 1440 = true := by quickRfl

theorem lt1 : allBlk 5760 (fun k => ltF (mF k)) 5760 = true := by quickRfl

end CFSG.KD.HS589207.MRecB

end
