module

public import Certificates.Kernel.LocalQT.Base.C7146D
public import Certificates.Kernel.LocalQT.Base.C4141H
public import Certificates.Data.Kernel.LocalQT.TreeT
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C7146

open CFSG.KC.LQT.TT CFSG.QuasithinUnique.K1.SporadicPerm

theorem hd : treeTH 8330 14 10 heB C4141.ta C4141.tb heProg heQp C4141.TF 34 8 10 100000 32 5 PK
    CK 16 128 PT CT = true := by
  quickRfl

end CFSG.KD.LQT.C7146

end
