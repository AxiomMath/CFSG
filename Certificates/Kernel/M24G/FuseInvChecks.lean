module

public import Certificates.Data.Kernel.M24G.FuseInv
public import Certificates.Data.Kernel.M24G.FuseFast
public import Certificates.Kernel.M24G.KzeroData
public import Certificates.Kernel.M24G.FusePosData

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.FuseC

open CFSG.KC.M24G

set_option maxHeartbeats 0 in
theorem fuseInv_okF : fuseInvF KzeroD.zL (balTree FuseS.aS) (balTree FuseS.bS) = true := by
  decide +kernel

end CFSG.KC.M24G.FuseC
