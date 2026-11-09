module

public import Certificates.Kernel.J2Dc.Defs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.J2Dc

open CFSG.KC.SLDc

theorem chunks : (List.range D.Rc.length).all (chunkOK C D) = true := by
  quickRfl

end CFSG.KD.J2Dc

end
