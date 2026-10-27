module

public import Certificates.Kernel.HN3.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HN3

theorem rels_ok : CFSG.KC.HN3.relsK mul regs CFSG.KD.FamHNSeed.ONE rels = true := by quickRfl

theorem orb5_ok : CFSG.KC.HN3.orbK mul vec vldV regs CFSG.KD.FamHNSeed.ONE g5 S5 I5 T5 O5 5 =
    true := by quickRfl

theorem orb2_ok : CFSG.KC.HN3.orbK mul vec vldV regs CFSG.KD.FamHNSeed.ONE g2 S2 I2 T2 O2 16 =
    true := by quickRfl

theorem orb3_ok : CFSG.KC.HN3.orbK mul vec vldV regs CFSG.KD.FamHNSeed.ONE g3 S3 I3 T3 O3 729 =
    true := by quickRfl

end CFSG.KD.HN3

end
