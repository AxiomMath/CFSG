module

public import Certificates.Kernel.P0Orb.Tab
public import Certificates.Kernel.P0Orb.Rows
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000

public section

open CFSG.KC.P0Orb CFSG.KD.P0Orb

#kc_each CFSG.KD.P0OrbR6 ch812462r6_ (fun i => grpOK AT RT BC BU 3000 8 CFSG.KD.P0OrbR6.rows i)
  0 75
#kc_each CFSG.KD.P0OrbR7 ch812462r7_ (fun i => grpOK AT RT BC BU 3600 8 CFSG.KD.P0OrbR7.rows i)
  0 75
#kc_each CFSG.KD.P0OrbR8 ch812462r8_ (fun i => grpOK AT RT BC BU 4200 8 CFSG.KD.P0OrbR8.rows i)
  0 86

end
