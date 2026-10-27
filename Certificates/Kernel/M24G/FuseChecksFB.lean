module

public import Certificates.Data.Kernel.M24G.FusePack
public import Certificates.Data.Kernel.M24G.FuseFast
public import Certificates.Data.Kernel.M24G.Replay
public import Certificates.Kernel.M24G.FuseData
public import Certificates.Kernel.M24G.FusePosData

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.FuseC

open CFSG.KC.M24G

set_option maxHeartbeats 0 in
theorem fuseOrbB_okF : replayOK (fun c => c) fuseStepsF fusePiBP 32000 FuseD.bL FuseD.bPar
    FuseD.bGen (balTree FuseS.bS) = true := by
  decide +kernel

end CFSG.KC.M24G.FuseC
