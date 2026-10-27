module

public import Certificates.Kernel.LocalQT.Base.C4061D
public import Certificates.Kernel.LocalQT.Base.C4061E
public import Certificates.Kernel.LocalQT.Base.C4061L
public import Certificates.Kernel.LocalQT.Base.C4143H
public import Certificates.Data.Kernel.LocalQT.X1R
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4061

open CFSG.KC.LQT.XR CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Setup.X1

theorem s2 : slp2H 4060 12 C4143.ta C4143.tb P2 TF 67 8 = true := by quickRfl

theorem ha : x1RA 4060 12 C4143.ta C4143.tb P2 ruQp WP TF 67 8 Wp.TF 324 16 323 428 409 456 5178
    5182 ruNodes1 ruNodes2 ruNodes3 = true := by
  quickRfl

theorem zh : zcH 12 ruB ruQp C4143.TF 16384 14 C4143.E 531 TF ruNodes1 ruNodes2 ruNodes3 = true := by
  quickRfl

end CFSG.KD.LQT.C4061

end
