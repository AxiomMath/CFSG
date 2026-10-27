module

public import Certificates.Kernel.HN1023016.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HN1023016

theorem chkW : chkWW hwm c0 keyc dep jb fus oth = true := by quickRfl

end CFSG.KD.HN1023016

end
