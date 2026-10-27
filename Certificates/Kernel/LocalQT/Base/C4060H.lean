module

public import Certificates.Kernel.LocalQT.Base.C4060D
public import Certificates.Kernel.LocalQT.Base.C4140
public import Certificates.Data.Kernel.LocalQT.RankB
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4060

open CFSG.KC.LQT.RB CFSG.QuasithinUnique.K1.SporadicPerm

theorem hd : rankBH 1100 11 9 hsB C4140.ta C4140.tb hsProg hsQp 9 100000 13 10 87 1 PK CK 8 48 PT
    CT = true := by
  quickRfl

end CFSG.KD.LQT.C4060

end
