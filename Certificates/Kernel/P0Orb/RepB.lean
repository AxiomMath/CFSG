module

public import Certificates.Kernel.P0Orb.Tab
public import Certificates.Kernel.P0Orb.Rows
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000

public section

open CFSG.KC.P0Orb CFSG.KD.P0Orb

#kc_each CFSG.KD.P0OrbR3 ch812462r3_ (fun i => grpOK AT RT BC BU 1200 8 CFSG.KD.P0OrbR3.rows i)
  0 75
#kc_each CFSG.KD.P0OrbR4 ch812462r4_ (fun i => grpOK AT RT BC BU 1800 8 CFSG.KD.P0OrbR4.rows i)
  0 75
#kc_each CFSG.KD.P0OrbR5 ch812462r5_ (fun i => grpOK AT RT BC BU 2400 8 CFSG.KD.P0OrbR5.rows i)
  0 75

end
