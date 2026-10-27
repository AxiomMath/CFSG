module

public import Certificates.Kernel.LocalQT.Base.C7145D
public import Certificates.Data.Kernel.LocalQT.TreeT
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieuInputs

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C7145

open CFSG.KC.LQT.TT CFSG.QuasithinUnique.K1.SporadicPerm

theorem hd : treeTH 24 5 10 (List.range 24) m24ta m24tb m24Prog m24Qp TF 29 8 10 100000 32 129 PK
    CK 16 128 PT CT = true := by
  quickRfl

end CFSG.KD.LQT.C7145

end
