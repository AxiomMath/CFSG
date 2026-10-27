module

public import Certificates.Kernel.HNFSub.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNFSub

theorem dist : CFSG.KC.HNFSub.distOK 88704 S7.segs = true := by quickRfl

end CFSG.KD.HNFSub

end
