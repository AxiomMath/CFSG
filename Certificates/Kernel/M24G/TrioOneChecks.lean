module

public import Certificates.Data.Kernel.M24G.TrioOne
public import Certificates.Kernel.M24G.TrioData
public import Certificates.Kernel.M24G.SextData
public import Certificates.Kernel.M24G.TrioOneData

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G

set_option maxHeartbeats 0 in
theorem fixCopW_ok : fixCopW prodBs TL SL W = true := by decide +kernel

end CFSG.KC.M24G
