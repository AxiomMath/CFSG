module

public import Certificates.Kernel.P0Vis.Tab
public import Certificates.Kernel.P0Vis.Rows
public import Certificates.Kernel.P0Orb.Tab
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000

public section

open CFSG.KC.P0Vis CFSG.KD.P0Orb CFSG.KD.P0Vis

#kc_each CFSG.KD.P0VisR2 ch812462v2_
  (fun i => vgrpOK ⟨AT, BT, BC, FK, FC⟩ RT FA YG 2400 16 CFSG.KD.P0VisR2.rows i) 0 75
#kc_each CFSG.KD.P0VisR3 ch812462v3_
  (fun i => vgrpOK ⟨AT, BT, BC, FK, FC⟩ RT FA YG 3600 16 CFSG.KD.P0VisR3.rows i) 0 81

end
