module

public import Certificates.Kernel.HNClsL.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000
set_option Elab.async false
set_option profiler true

namespace CFSG.KD.HNClsL

theorem chkC : chkL poolC gensC nQC linesC fuseC wlC witsC trC = true := by quickRfl

end CFSG.KD.HNClsL

end
