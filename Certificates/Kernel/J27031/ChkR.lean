module

public import Certificates.Kernel.J27031.M
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.DcKN

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.J27031

open CFSG.KC.DcK

theorem r_hd : enumHd 315 BK 200 ER = true := by quickRfl

theorem r_el : elemsK 315 BK rt 3 ER 0 128 = true := by quickRfl

theorem r_orb : orbCK 315 rt 3 QF vtF lbF = true := by quickRfl

end CFSG.KD.J27031

end
