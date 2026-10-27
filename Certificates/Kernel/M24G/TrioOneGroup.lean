module

public import Certificates.Data.Kernel.M24G.TrioOne

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G

set_option maxHeartbeats 0 in
theorem groupL_ok : groupL = true := by decide +kernel

end CFSG.KC.M24G
