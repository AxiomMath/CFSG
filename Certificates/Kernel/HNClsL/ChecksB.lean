module

public import Certificates.Kernel.HNClsL.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000
set_option Elab.async false
set_option profiler true

namespace CFSG.KD.HNClsL

theorem chkB : chkL poolB gensB nQB linesB fuseB wlB witsB trB = true := by quickRfl

end CFSG.KD.HNClsL

end
