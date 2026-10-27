module

public import Certificates.Kernel.P0Vis.Tab
public import Certificates.Kernel.P0Vis.Rows
public import Certificates.Kernel.P0Orb.Tab
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000

public section

open CFSG.KC.P0Vis CFSG.KD.P0Orb CFSG.KD.P0Vis

#kc_each CFSG.KD.P0VisR0 ch812462v0_
  (fun i => vgrpOK ⟨AT, BT, BC, FK, FC⟩ RT FA YG 0 16 CFSG.KD.P0VisR0.rows i) 0 75
#kc_each CFSG.KD.P0VisR1 ch812462v1_
  (fun i => vgrpOK ⟨AT, BT, BC, FK, FC⟩ RT FA YG 1200 16 CFSG.KD.P0VisR1.rows i) 0 75

end
