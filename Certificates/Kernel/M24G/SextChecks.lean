module

public import Certificates.Data.Kernel.M24G.ListChecks
public import Certificates.Kernel.M24G.SextData
public import Certificates.Kernel.M24G.OctData

set_option maxRecDepth 100000

public section

namespace CFSG.KC.M24G.SextC

open CFSG.KC.M24G CFSG.KC.ONanSmall CFSG.Quasithin.H13.AS91.M24G

theorem length : SL.length = 1771 := by decide +kernel

theorem items : SL.all sextItem = true := by decide +kernel

theorem tets : tetsOK OctD.O (posTree Native.keyL SL) = true := by decide +kernel

end CFSG.KC.M24G.SextC
