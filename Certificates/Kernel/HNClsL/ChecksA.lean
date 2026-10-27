module

public import Certificates.Kernel.HNClsL.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000
set_option Elab.async false
set_option profiler true

namespace CFSG.KD.HNClsL

theorem chkA : chkL poolA gensA nQA linesA fuseA wlA witsA trA = true := by quickRfl

end CFSG.KD.HNClsL

end
