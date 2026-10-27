module

public import Certificates.Kernel.HS589207.M
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.BfsRecK

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HS589207.MRecA

open CFSG.KC.DcK CFSG.KC.DcHSOutK CFSG.KC.Enum CFSG.Quasithin.H13.LocDbl.HSLoc

theorem hd : enumHd 100 B100 12000 EM = true := by quickRfl

theorem s0 : elemsK 100 B100 GM 2 EM 0 1440 = true := by quickRfl

theorem s1 : elemsK 100 B100 GM 2 EM 1440 1440 = true := by quickRfl

theorem s2 : elemsK 100 B100 GM 2 EM 2880 1440 = true := by quickRfl

theorem s3 : elemsK 100 B100 GM 2 EM 4320 1440 = true := by quickRfl

theorem lt0 : allBlk 0 (fun k => ltF (mF k)) 5760 = true := by quickRfl

end CFSG.KD.HS589207.MRecA

end
