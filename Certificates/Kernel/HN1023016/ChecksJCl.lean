module

public import Certificates.Kernel.HN1023016.DataCl
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HN1023016

theorem chkJCl : chkJClW prg px wg wr hw rel fus bw hwm ce lp lab = true := by quickRfl

end CFSG.KD.HN1023016

end
