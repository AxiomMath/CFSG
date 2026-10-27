module

public import Certificates.Kernel.HN3.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HN3

theorem prog_ok : CFSG.KC.HN3.progK mul (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2)
    CFSG.KD.FamHNSeed.ONE prog regs = true := by quickRfl

end CFSG.KD.HN3

end
