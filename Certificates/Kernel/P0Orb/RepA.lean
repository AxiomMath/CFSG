module

public import Certificates.Kernel.P0Orb.Tab
public import Certificates.Kernel.P0Orb.Rows
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000

public section

open CFSG.KC.P0Orb CFSG.KD.P0Orb

#kc_each CFSG.KD.P0OrbR0 ch812462r0_ (fun i => grpOK AT RT BC BU 0 8 CFSG.KD.P0OrbR0.rows i) 0 1
#kc_each CFSG.KD.P0OrbR1 ch812462r1_ (fun i => grpOK AT RT BC BU 1 8 CFSG.KD.P0OrbR1.rows i) 0 75
#kc_each CFSG.KD.P0OrbR2 ch812462r2_ (fun i => grpOK AT RT BC BU 600 8 CFSG.KD.P0OrbR2.rows i)
  0 75

end
